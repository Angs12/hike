(* Constructors missing from LLVM's OCaml bindings, using the same C API. *)
external fence : Llvm.AtomicOrdering.t -> Llvm.llbuilder -> unit
  = "hike_build_fence"

external cmpxchg :
  Llvm.llvalue -> Llvm.llvalue -> Llvm.llvalue -> Llvm.llbuilder -> Llvm.llvalue
  = "hike_build_cmpxchg"

external set_seq_cst : Llvm.llvalue -> unit = "hike_atomic_load_seq_cst"

(* Negation has no LLVM atomicrmw opcode. Retry with the observed cell. *)
let negate llvm_module ptr bits builder =
  let llvm_ctx = Llvm.module_context llvm_module in
  let ty = Llvm.integer_type llvm_ctx bits in
  let name = Printf.sprintf "hike.atomic.neg.%d" bits in
  let fn = match Llvm.lookup_function name llvm_module with
    | Some fn -> fn
    | None ->
      let fn_ty = Llvm.function_type ty [|Llvm.type_of ptr|] in
      let fn = Llvm.define_function name fn_ty llvm_module in
      Llvm.set_linkage Llvm.Linkage.Internal fn;
      let entry = Llvm.entry_block fn in
      let loop = Llvm.append_block llvm_ctx "retry" fn in
      let done_ = Llvm.append_block llvm_ctx "done" fn in
      let b = Llvm.builder_at_end llvm_ctx entry in
      let address = Llvm.param fn 0 in
      let seed = Llvm.build_load ty address "seed" b in
      set_seq_cst seed;
      Llvm.set_alignment 1 seed;
      ignore (Llvm.build_br loop b);
      Llvm.position_at_end loop b;
      let expected = Llvm.build_phi [seed,entry] "expected" b in
      let desired = Llvm.build_neg expected "desired" b in
      let result = cmpxchg address expected desired b in
      Llvm.set_alignment 1 result;
      let observed = Llvm.build_extractvalue result 0 "observed" b in
      let success = Llvm.build_extractvalue result 1 "success" b in
      Llvm.add_incoming (observed,loop) expected;
      ignore (Llvm.build_cond_br success done_ loop b);
      Llvm.position_at_end done_ b;
      ignore (Llvm.build_ret observed b);
      fn in
  let fn_ty = Llvm.function_type ty [|Llvm.type_of ptr|] in
  Llvm.build_call fn_ty fn [|ptr|] "" builder
