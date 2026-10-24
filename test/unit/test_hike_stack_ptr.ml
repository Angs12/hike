(* Pins for the stack storage builder: every stack storage is a real LLVM
   alloca, one per layout region, its mem var the region's, its [rel] the
   entry-relative base of the range.  One Alcotest group per pin; each pin
   builds its own LLVM context, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module Model = Hike_stack_model
module Stack_ptr = Hike_stack_ptr

(* A real function to build into, the builder at the end of its entry block
   (the emitter's [create_sub] position).  Allocas need an insertion point. *)
let with_builder f =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "stack_ptr_test" in
  let fn_ty = Llvm.function_type (Llvm.void_type llvm_ctx) [||] in
  let fn = Llvm.define_function "sp_fn" fn_ty llvm_module in
  let llvm_builder = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in
  Fun.protect
    ~finally:(fun () -> Llvm.dispose_module llvm_module; Llvm.dispose_context llvm_ctx)
    (fun () ->
      f llvm_ctx llvm_module llvm_builder;
      Base.Option.iter (Llvm_analysis.verify_module llvm_module) ~f:Alcotest.fail)

let layout_of ?(window_param = false) ?(runtime_residue = false) regions
    : Model.sub_layout =
  { regions; window_param; runtime_residue }

(* The absolute segment-line position of a frame offset, exactly as the
   producer stamps it: [base + o]. *)
let pos (o : int64) : int64 = Int64.add Model.segment_base o

let alloca_p (v : Llvm.llvalue) : bool =
  match Llvm.classify_value v with
  | Llvm.ValueKind.Instruction Llvm.Opcode.Alloca -> true
  | _ -> false

(* A region storage is its alloca, or the alloca GEP'd to the region's
   model-aligned start. *)
let storage_base_p (v : Llvm.llvalue) : bool =
  alloca_p v
  ||
  match Llvm.classify_value v with
  | Llvm.ValueKind.Instruction Llvm.Opcode.GetElementPtr ->
    Llvm.num_operands v = 2 && alloca_p (Llvm.operand v 0)
  | _ -> false

let tests : unit Alcotest.test list =
  [

    pin "SPTR-02"
      "one region is one storage: the region's mem var, its entry-relative \
       base, and a real alloca of the range's bytes"
      (fun () ->
        with_builder (fun llvm_ctx llvm_module llvm_builder ->
        let regions =
          [ { Model.Sub_layout.r_id = 3;
              r_lo = pos (-24L);
              r_hi = pos (-17L);
              r_bytes = 16L } ]
        in
        let { Stack_ptr.storages; _ } =
          Stack_ptr.build_frame ~llvm_ctx ~llvm_builder ~addr_bits:64 ~word:8
            (layout_of regions)
        in
        ignore (Llvm.build_ret_void llvm_builder);
        check "SPTR-02"
          (match storages with
          | [ s ] ->
              Var.same s.mem (Model.region_mem ~addr_bits:64 3)
              && Int64.equal s.rel (-24L)
              && alloca_p s.base
              && Int.equal (Llvm.alignment s.base) 16
              && contains_substring (Llvm.string_of_llvalue s.base) "alloca [16 x i8], align 16"
          | _ -> false)));

    pin "SPTR-04"
      "a runtime residue is the region below the cursor: the residue base \
       derives from the entry call by GEPs, a carved region's storage is its \
       alloca (offset to its model-aligned start), and the helpers are weak \
       noinline definitions with the cursor attributes"
      (fun () ->
        with_builder (fun llvm_ctx llvm_module llvm_builder ->
        let regions =
          [ { Model.Sub_layout.r_id = 0;
              r_lo = pos (-48L);
              r_hi = pos 15L;
              r_bytes = 80L };
            { Model.Sub_layout.r_id = 2;
              r_lo = pos (-96L);
              r_hi = pos (-81L);
              r_bytes = 16L } ]
        in
        let { Stack_ptr.storages; runtime_top } =
          Stack_ptr.build_frame ~llvm_ctx ~llvm_builder ~addr_bits:64 ~word:8
            (layout_of ~runtime_residue:true regions)
        in
        Stack_ptr.set_cursor ~llvm_ctx llvm_builder
          (Base.Option.value_exn runtime_top);
        ignore (Llvm.build_ret_void llvm_builder);
        let ir = Llvm.string_of_llmodule llvm_module in
        check "SPTR-04"
          (match storages, runtime_top with
          | [ residue; carved ], Some top ->
              (not (alloca_p residue.base))
              && storage_base_p carved.base
              && Int64.equal residue.rel (-48L)
              && contains_substring ir "%rstack_top = call ptr @hike_rstack_enter()"
              && contains_substring ir "%rstack_entry = getelementptr i8, ptr %rstack_top, i64 -24"
              && Llvm.value_name top = "rstack_top"
              && contains_substring ir "define weak noalias ptr @hike_rstack_enter()"
              && contains_substring ir "define weak void @hike_rstack_set(ptr nocapture"
              && contains_substring ir "memory(inaccessiblemem: write)"
              && contains_substring ir "noinline"
              && contains_substring ir "@hike_rstack_cur = weak thread_local global"
          | _ -> false)));

    pin "SPTR-05"
      "a bounded layout carries no runtime-stack helper"
      (fun () ->
        with_builder (fun llvm_ctx llvm_module llvm_builder ->
        let regions =
          [ { Model.Sub_layout.r_id = 0;
              r_lo = pos (-48L);
              r_hi = pos 15L;
              r_bytes = 80L } ]
        in
        let { Stack_ptr.storages; runtime_top } =
          Stack_ptr.build_frame ~llvm_ctx ~llvm_builder ~addr_bits:64 ~word:8
            (layout_of regions)
        in
        ignore (Llvm.build_ret_void llvm_builder);
        let ir = Llvm.string_of_llmodule llvm_module in
        check "SPTR-05"
          (Base.Option.is_none runtime_top
           && (match storages with [ s ] -> storage_base_p s.base | _ -> false)
           && not (contains_substring ir "hike_rstack"))));

    pin "SPTR-06"
      "the optimizer sees a runtime frame as a fresh object: a frame store \
       survives an unknown call and a store through an argument"
      (fun () ->
        match Unix.system "command -v opt >/dev/null 2>&1" with
        | Unix.WEXITED 0 ->
            with_builder (fun llvm_ctx llvm_module sp_b ->
            ignore (Llvm.build_ret_void sp_b);
            let i64 = Llvm.i64_type llvm_ctx in
            let ptr = Llvm.pointer_type llvm_ctx in
            let unknown =
              Llvm.declare_function "unknown" (Llvm.function_type i64 [||])
                llvm_module
            in
            let fn =
              Llvm.define_function "frame"
                (Llvm.function_type i64 [| ptr |]) llvm_module
            in
            let b = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in
            let regions =
              [ { Model.Sub_layout.r_id = 0;
                  r_lo = pos (-48L);
                  r_hi = pos 15L;
                  r_bytes = 80L } ]
            in
            let { Stack_ptr.storages; runtime_top } =
              Stack_ptr.build_frame ~llvm_ctx ~llvm_builder:b ~addr_bits:64
                ~word:8 (layout_of ~runtime_residue:true regions)
            in
            let top = Base.Option.value_exn runtime_top in
            let cell =
              Llvm.build_gep (Llvm.i8_type llvm_ctx)
                (List.hd storages).base
                [| Llvm.const_int i64 16 |] "cell" b
            in
            ignore (Llvm.build_store (Llvm.const_int i64 42) cell b);
            Stack_ptr.set_cursor ~llvm_ctx b cell;
            ignore (Llvm.build_store (Llvm.const_int i64 7) (Llvm.param fn 0) b);
            ignore
              (Llvm.build_call (Llvm.function_type i64 [||]) unknown [||] "" b);
            let v = Llvm.build_load i64 cell "v" b in
            Stack_ptr.set_cursor ~llvm_ctx b top;
            ignore (Llvm.build_ret v b);
            let src = Filename.temp_file "sptr06" ".ll" in
            let oc = open_out src in
            output_string oc (Llvm.string_of_llmodule llvm_module);
            close_out oc;
            let out = src ^ ".opt.ll" in
            let rc =
              Sys.command
                (Printf.sprintf "opt -O2 -S %s -o %s"
                   (Filename.quote src) (Filename.quote out))
            in
            Alcotest.(check int) "optimizer succeeds" 0 rc;
            let text = In_channel.with_open_bin out In_channel.input_all in
            Sys.remove src;
            Sys.remove out;
            check "SPTR-06"
              (contains_substring text "ret i64 42"
               && not (contains_substring text "load i64")))
        | _ -> Alcotest.fail "SPTR-06 requires opt on PATH");

  ]

let () = run "hike_stack_ptr" tests
