(* The width-coercion pass. *)
open Bap.Std

  val coerce_exp : exp -> exp
  val coerce_block : blk term -> blk term
  val coerce_program : program term -> program term
