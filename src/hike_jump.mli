(* T13 — the jump compiler (construction).  Exposes the BIR rewrite
   only: pipeline registration is the slot-window phase. *)

open Bap.Std

(** [compile_sub sub]: rewrites jcc flag idioms into the simplest
    equivalent value comparisons.  A cond whose flags have dominating
    single defs in the same block compiles (the consumed flag defs
    whose only use was the rewritten jump are dropped); everything
    else is the identity. *)
val compile_sub : sub term -> sub term

(** [compile_program prog]: [compile_sub] over every sub. *)
val compile_program : program term -> program term
