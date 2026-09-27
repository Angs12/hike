(* One home for the stack storage and its addresses: every stack storage
   is an LLVM alloca, and a stack address is a pointer into one. *)

open Bap.Std

module Model = Hike_stack_model
module Abi = Hike_abi

type storage = {
  mem : Var.t;
  base : Llvm.llvalue;
  rel : int64;
}

(* The sub's storages: one alloca per layout region, in layout order. *)
let build ~(llvm_ctx : Llvm.llcontext) ~(llvm_builder : Llvm.llbuilder)
    (layout : Model.Sub_layout.t) : storage list =
  Base.List.map layout.Model.Sub_layout.regions
    ~f:(fun (id, (lo, _), bytes) ->
      let base =
        Llvm.build_alloca
          (Llvm.array_type (Llvm.i8_type llvm_ctx) (Int64.to_int bytes))
          (Model.region_name id)
          llvm_builder
      in
      Llvm.set_alignment Abi.stack_align base;
      { mem = Model.region_mem id;
        base;
        rel = Stdlib.Int64.sub lo Model.segment_base })

(* The storage's base GEP'd at the address's byte index: both the address
   and the base are relative to the sub's entry SP, so the index is
   [a − stack0 − rel].  [rel = 0] is a storage whose base IS the entry
   line (the caller window): the index is [a − stack0], no difference. *)
let ptr_of ~(llvm_ctx : Llvm.llcontext) ~(llvm_builder : Llvm.llbuilder)
    ~(base : Llvm.llvalue) ~(rel : int64) ~(stack0 : Llvm.llvalue)
    (a : Llvm.llvalue) : Llvm.llvalue =
  let idx =
    let rel_addr = Llvm.build_sub a stack0 "reg_rel" llvm_builder in
    if Int64.equal rel 0L then rel_addr
    else
      Llvm.build_sub rel_addr
        (Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) rel false)
        "" llvm_builder
  in
  Llvm.build_gep (Llvm.i8_type llvm_ctx) base [| idx |] "" llvm_builder
