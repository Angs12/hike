(* One home for the stack storage and its addresses: every stack storage
   is an LLVM alloca, and a stack address is a pointer into one. *)

open Bap.Std

module Model = Hike_stack_model
module Abi = Hike_abi

type storage = {
  id : int;
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
      { id;
        mem = Model.region_mem id;
        base;
        rel = Stdlib.Int64.sub lo Model.segment_base })
