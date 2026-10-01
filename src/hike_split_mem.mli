(* Node fission. *)
open Bap.Std

(* One def's fission: the later memory nodes become fresh virtual
   loads before it. *)
val split_def : def term -> def term list

  val split_sub : sub term -> sub term
  val normalize : program term -> program term
