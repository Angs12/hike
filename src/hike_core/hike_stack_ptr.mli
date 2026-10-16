(* One home for the stack storage and its addresses: every stack storage
   is an LLVM alloca, or the entry region of the per-thread runtime
   stack, and a stack address is a pointer into one. *)

open Bap.Std

type storage = {
  id : int;             (* the region id (the residue is 0) *)
  mem : Var.t;          (* the storage's memory variable *)
  base : Llvm.llvalue;  (* the alloca, or the runtime residue's base pointer *)
  rel : int64;          (* the entry-relative base of its range *)
}

type frame = {
  storages : storage list;
  runtime_top : Llvm.llvalue option;
      (* a runtime sub's cursor at entry, restored at every exit *)
}

(* The per-thread reservation of the runtime stack, in bytes. *)
val runtime_stack_bytes : int64

(* The sub's storages: one alloca per layout region in layout order; a
   runtime sub's residue is the region below the cursor instead, and
   the frame carries the cursor value. *)
val build_frame :
  llvm_ctx:Llvm.llcontext ->
  llvm_builder:Llvm.llbuilder ->
  addr_bits:int ->
  word:int ->
  Hike_stack_model.Sub_layout.t ->
  frame

(* The cursor moves to a pointer (the helper defined on first use). *)
val set_cursor :
  llvm_ctx:Llvm.llcontext -> Llvm.llbuilder -> Llvm.llvalue -> unit
