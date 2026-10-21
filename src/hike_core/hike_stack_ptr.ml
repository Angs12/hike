(* One home for the stack storage and its addresses: every stack storage
   is an LLVM alloca, or the entry region of the per-thread runtime
   stack, and a stack address is a pointer into one. *)

open Bap.Std

module Model = Hike_stack_model
module Abi = Hike_abi

type storage = {
  id : int;
  mem : Var.t;
  base : Llvm.llvalue;
  rel : int64;
}

(* The per-thread runtime stack: one lazily mapped region with a guard
   page below it and a thread-local cursor at its lowest byte in use.
   The helpers are weak, noinline definitions, so the optimizer reads
   only their attributes: [enter] returns a fresh 16-aligned object
   (noalias), and [set] publishes the cursor's address and nothing else
   (it neither reads nor captures the frame).  The helper ABI is
   x86-64: pointers and mmap/munmap size_t operands are i64. *)

(* The reservation per thread: a resource, not an analysis bound. *)
let runtime_stack_bytes : int64 = 268_435_456L

let guard_bytes : int64 = 4096L

let enter_name = "hike_rstack_enter"
let set_name = "hike_rstack_set"

(* [memory(inaccessiblemem: write)]: the cursor is invisible to the
   program's own memory. *)
let memory_inaccessible_write = 8L

let fn_attr ctx fn name v =
  Llvm.add_function_attr fn (Llvm.create_enum_attr ctx name v)
    Llvm.AttrIndex.Function

let weak_noinline ctx fn =
  Llvm.set_linkage Llvm.Linkage.Weak fn;
  fn_attr ctx fn "noinline" 0L;
  fn_attr ctx fn "nounwind" 0L

let declare md name ret args =
  let ty = Llvm.function_type ret args in
  (ty, Llvm.declare_function name ty md)

let tls_cell md ptr name =
  let g = Llvm.define_global name (Llvm.const_null ptr) md in
  Llvm.set_thread_local true g;
  Llvm.set_linkage Llvm.Linkage.Weak g;
  g

(* A thread's exit unmaps its region and clears the cursor. *)
let define_free ~llvm_ctx md ~total ~cur ~base =
  let ptr = Llvm.pointer_type llvm_ctx in
  let i64 = Llvm.i64_type llvm_ctx and i32 = Llvm.i32_type llvm_ctx in
  let munmap_ty, munmap = declare md "munmap" i32 [| ptr; i64 |] in
  let free =
    Llvm.define_function "hike_rstack_free"
      (Llvm.function_type (Llvm.void_type llvm_ctx) [| ptr |]) md
  in
  weak_noinline llvm_ctx free;
  let b = Llvm.builder_at_end llvm_ctx (Llvm.entry_block free) in
  let m = Llvm.build_load ptr base "" b in
  ignore
    (Llvm.build_call munmap_ty munmap
       [| m; Llvm.const_of_int64 i64 total false |] "" b);
  ignore (Llvm.build_store (Llvm.const_null ptr) cur b);
  ignore (Llvm.build_store (Llvm.const_null ptr) base b);
  ignore (Llvm.build_ret_void b);
  free

let define_enter ~llvm_ctx md ~reserve : Llvm.llvalue =
  let ptr = Llvm.pointer_type llvm_ctx in
  let i64 = Llvm.i64_type llvm_ctx and i32 = Llvm.i32_type llvm_ctx in
  let void = Llvm.void_type llvm_ctx in
  let cur = tls_cell md ptr "hike_rstack_cur" in
  let base = tls_cell md ptr "hike_rstack_base" in
  let total = Int64.add reserve guard_bytes in
  let mmap_ty, mmap =
    declare md "mmap" ptr [| ptr; i64; i32; i32; i32; i64 |] in
  let mprotect_ty, mprotect = declare md "mprotect" i32 [| ptr; i64; i32 |] in
  let trap_ty, trap = declare md "llvm.trap" void [||] in
  let atexit_ty, atexit =
    declare md "__cxa_thread_atexit_impl" i32 [| ptr; ptr; ptr |] in
  Llvm.set_linkage Llvm.Linkage.External_weak atexit;
  let mask_ty, mask = declare md "llvm.ptrmask.p0.i64" ptr [| ptr; i64 |] in
  let free = define_free ~llvm_ctx md ~total ~cur ~base in
  let enter =
    Llvm.define_function enter_name (Llvm.function_type ptr [||]) md in
  weak_noinline llvm_ctx enter;
  Llvm.add_function_attr enter (Llvm.create_enum_attr llvm_ctx "noalias" 0L)
    Llvm.AttrIndex.Return;
  let block name = Llvm.append_block llvm_ctx name enter in
  let b = Llvm.builder_at_end llvm_ctx (Llvm.entry_block enter) in
  let init = block "init" and fail = block "fail" and ok = block "ok" in
  let reg = block "register" and join = block "join" in
  let c = Llvm.build_load ptr cur "cur" b in
  let first = Llvm.build_icmp Llvm.Icmp.Eq c (Llvm.const_null ptr) "first" b in
  let entry_bb = Llvm.insertion_block b in
  ignore (Llvm.build_cond_br first init join b);
  Llvm.position_at_end init b;
  let m =
    Llvm.build_call mmap_ty mmap
      [| Llvm.const_null ptr; Llvm.const_of_int64 i64 total false;
         Llvm.const_int i32 3; Llvm.const_int i32 0x4022;
         Llvm.const_int i32 (-1); Llvm.const_of_int64 i64 0L false |]
      "map" b
  in
  let bad =
    Llvm.build_icmp Llvm.Icmp.Eq m
      (Llvm.const_inttoptr (Llvm.const_of_int64 i64 (-1L) true) ptr) "bad" b
  in
  ignore (Llvm.build_cond_br bad fail ok b);
  Llvm.position_at_end fail b;
  ignore (Llvm.build_call trap_ty trap [||] "" b);
  ignore (Llvm.build_unreachable b);
  Llvm.position_at_end ok b;
  ignore
    (Llvm.build_call mprotect_ty mprotect
       [| m; Llvm.const_of_int64 i64 guard_bytes false; Llvm.const_int i32 0 |]
       "" b);
  let top =
    Llvm.build_gep (Llvm.i8_type llvm_ctx) m
      [| Llvm.const_of_int64 i64 total false |] "top" b
  in
  ignore (Llvm.build_store m base b);
  ignore (Llvm.build_store top cur b);
  let have =
    Llvm.build_icmp Llvm.Icmp.Ne atexit (Llvm.const_null ptr) "have" b in
  ignore (Llvm.build_cond_br have reg join b);
  Llvm.position_at_end reg b;
  ignore
    (Llvm.build_call atexit_ty atexit [| free; Llvm.const_null ptr; free |] "" b);
  ignore (Llvm.build_br join b);
  Llvm.position_at_end join b;
  let v = Llvm.build_phi [ (c, entry_bb); (top, ok); (top, reg) ] "v" b in
  let aligned =
    Llvm.build_call mask_ty mask
      [| v; Llvm.const_of_int64 i64 (Int64.of_int (-Abi.stack_align)) true |]
      "aligned" b
  in
  ignore (Llvm.build_ret aligned b);
  enter

let define_set ~llvm_ctx md : Llvm.llvalue =
  let ptr = Llvm.pointer_type llvm_ctx in
  let cur =
    match Llvm.lookup_global "hike_rstack_cur" md with
    | Some g -> g
    | None -> failwith "hike-emit: the runtime stack's cursor is missing"
  in
  let set =
    Llvm.define_function set_name
      (Llvm.function_type (Llvm.void_type llvm_ctx) [| ptr |]) md
  in
  weak_noinline llvm_ctx set;
  fn_attr llvm_ctx set "memory" memory_inaccessible_write;
  (* The bindings predate [captures(address)]; the optimizer reads
     [nocapture] as [captures(none)]. *)
  Llvm.add_function_attr set
    (Llvm.create_enum_attr llvm_ctx "nocapture" 0L)
    (Llvm.AttrIndex.Param 0);
  let b = Llvm.builder_at_end llvm_ctx (Llvm.entry_block set) in
  ignore (Llvm.build_store (Llvm.param set 0) cur b);
  ignore (Llvm.build_ret_void b);
  set

(* The helpers, defined on first use: only a module with a runtime sub
   carries them. *)
let helpers ~llvm_ctx md : Llvm.llvalue * Llvm.llvalue =
  let enter =
    match Llvm.lookup_function enter_name md with
    | Some fn -> fn
    | None -> define_enter ~llvm_ctx md ~reserve:runtime_stack_bytes
  in
  let set =
    match Llvm.lookup_function set_name md with
    | Some fn -> fn
    | None -> define_set ~llvm_ctx md
  in
  (enter, set)

let module_of b = Llvm.global_parent (Llvm.block_parent (Llvm.insertion_block b))

(* The 16-aligned cursor at a runtime sub's entry. *)
let enter ~llvm_ctx b : Llvm.llvalue =
  let fn, _ = helpers ~llvm_ctx (module_of b) in
  Llvm.build_call
    (Llvm.function_type (Llvm.pointer_type llvm_ctx) [||]) fn [||]
    "rstack_top" b

(* The cursor moves to [p]. *)
let set_cursor ~llvm_ctx b (p : Llvm.llvalue) : unit =
  let _, fn = helpers ~llvm_ctx (module_of b) in
  let ty =
    Llvm.function_type (Llvm.void_type llvm_ctx)
      [| Llvm.pointer_type llvm_ctx |]
  in
  ignore (Llvm.build_call ty fn [| p |] "" b)

type frame = {
  storages : storage list;
  runtime_top : Llvm.llvalue option;
}

let align_up (n : int64) : int64 =
  let a = Int64.of_int Abi.stack_align in
  Int64.mul (Int64.div (Int64.add n (Int64.pred a)) a) a

(* The sub's storages in layout order: an alloca per region.  A runtime
   sub's residue is instead the region the cursor leaves below it: its
   entry sits one word under a 16-aligned address that clears the fixed
   above-entry window, so the anchor keeps the alloca's alignment. *)
let build_frame ~(llvm_ctx : Llvm.llcontext) ~(llvm_builder : Llvm.llbuilder)
    ~(addr_bits : int) ~(word : int) (layout : Model.Sub_layout.t) : frame =
  let i8 = Llvm.i8_type llvm_ctx and i64 = Llvm.i64_type llvm_ctx in
  let runtime_top =
    if layout.Model.Sub_layout.runtime_residue then
      Some (enter ~llvm_ctx llvm_builder)
    else None
  in
  let storages =
    Base.List.map layout.Model.Sub_layout.regions
      ~f:(fun { Model.Sub_layout.r_id = id; r_lo = lo; r_hi = hi;
                r_bytes = bytes } ->
        let rel = Stdlib.Int64.sub lo Model.segment_base in
        let base =
          match runtime_top with
          | Some top when Int.equal id Model.residue_id ->
            let window = Int64.succ (Int64.sub hi Model.segment_base) in
            let below_top = Int64.add (align_up window) (Int64.of_int word) in
            let entry =
              Llvm.build_gep i8 top
                [| Llvm.const_of_int64 i64 (Int64.neg below_top) true |]
                "rstack_entry" llvm_builder
            in
            Llvm.build_gep i8 entry [| Llvm.const_of_int64 i64 rel true |]
              (Model.region_name id) llvm_builder
          | _ ->
            let base =
              Llvm.build_alloca
                (Llvm.array_type i8 (Int64.to_int bytes))
                (Model.region_name id)
                llvm_builder
            in
            Llvm.set_alignment Abi.stack_align base;
            base
        in
        { id; mem = Model.region_mem ~addr_bits id; base; rel })
  in
  { storages; runtime_top }
