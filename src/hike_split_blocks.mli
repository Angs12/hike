(* The block/jmp split and the free-register seam. *)
open Bap.Std

  val split_sub : sub term -> sub term
  val normalize : program term -> program term

  (** The BIR's free registers over its explicit edges, memory vars
      dropped. *)
  val free_regs : sub term -> var list
