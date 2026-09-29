(* One home for the stack storage and its addresses: every stack storage
   is an LLVM alloca, and a stack address is a pointer into one. *)

open Bap.Std

type storage = {
  id : int;             (* the region id (the residue is 0) *)
  mem : Var.t;          (* the storage's memory variable *)
  base : Llvm.llvalue;  (* the alloca itself *)
  rel : int64;          (* the entry-relative base of its range *)
}

val build :
  llvm_ctx:Llvm.llcontext ->
  llvm_builder:Llvm.llbuilder ->
  Hike_stack_model.Sub_layout.t ->
  storage list
