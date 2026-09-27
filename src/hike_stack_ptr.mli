(* One home for the stack storage and its addresses: every stack storage
   is an LLVM alloca, and a stack address is a pointer into one. *)

open Bap.Std

type storage = {
  mem : Var.t;          (* the storage's memory variable *)
  base : Llvm.llvalue;  (* the alloca itself *)
  rel : int64;          (* the entry-relative base of its range *)
}

val build :
  llvm_ctx:Llvm.llcontext ->
  llvm_builder:Llvm.llbuilder ->
  Hike_stack_model.Sub_layout.t ->
  storage list

(* The pointer form of an address into a storage: the storage's base
   GEP'd at the address's byte index, the address normalized by the sub's
   entry SP and the storage's own base offset.  An address VALUE stays an
   i64; this is the one place it becomes the pointer it denotes.  A
   [rel] of 0 is a storage whose base is the entry line (the caller
   window). *)
val ptr_of :
  llvm_ctx:Llvm.llcontext ->
  llvm_builder:Llvm.llbuilder ->
  base:Llvm.llvalue ->
  rel:int64 ->
  stack0:Llvm.llvalue ->
  Llvm.llvalue ->
  Llvm.llvalue
