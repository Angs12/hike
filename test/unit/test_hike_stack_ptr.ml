(* Pins for the stack storage builder: every stack storage is a real LLVM
   alloca, one per layout region, its mem var the region's, its [rel] the
   entry-relative base of the range.  One Alcotest group per pin; each pin
   builds its own LLVM context, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module Model = Hike__Hike_stack_model
module Stack_ptr = Hike__Hike_stack_ptr

(* A real function to build into, the builder at the end of its entry block
   (the emitter's [create_sub] position).  Allocas need an insertion point. *)
let make_builder () =
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "stack_ptr_test" in
  let fn_ty = Llvm.function_type (Llvm.void_type llvm_ctx) [||] in
  let fn = Llvm.define_function "sp_fn" fn_ty llvm_module in
  let llvm_builder = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in
  (llvm_ctx, llvm_module, llvm_builder)

let layout_of ?(window_param = false) regions : Model.sub_layout =
  { regions; window_param }

(* The absolute segment-line position of a frame offset, exactly as the
   producer stamps it: [base + o]. *)
let pos (o : int64) : int64 = Int64.add Model.segment_base o

let alloca_p (v : Llvm.llvalue) : bool =
  match Llvm.classify_value v with
  | Llvm.ValueKind.Instruction Llvm.Opcode.Alloca -> true
  | _ -> false

let tests : unit Alcotest.test list =
  [


    pin "SPTR-02"
      "one region is one storage: the region's mem var, its entry-relative \
       base, and a real alloca of the range's bytes"
      (fun () ->
        let llvm_ctx, llvm_module, llvm_builder = make_builder () in
        let regions =
          [ { Model.Sub_layout.r_id = 3;
              r_lo = pos (-24L);
              r_hi = pos (-17L);
              r_bytes = 16L } ]
        in
        let storages =
          Stack_ptr.build ~llvm_ctx ~llvm_builder (layout_of regions)
        in
        ignore (Llvm.build_ret_void llvm_builder);
        let ir = Llvm.string_of_llmodule llvm_module in
        check "SPTR-02"
          (match storages with
          | [ s ] ->
              Var.same s.mem (Model.region_mem 3)
              && Int64.equal s.rel (-24L)
              && alloca_p s.base
              && String.equal (Llvm.value_name s.base) "stack_r3"
              && Int.equal (Llvm.alignment s.base) 16
              && contains_substring ir "%stack_r3 = alloca [16 x i8], align 16"
          | _ -> false));



  ]

let () = run "hike_stack_ptr" tests
