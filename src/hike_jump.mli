(* T13 — the jump compiler (construction).  Exposes the BIR rewrite
   only: pipeline registration is the slot-window phase. *)

open Bap.Std

(** [compile_sub sub]: rewrites jcc flag idioms into the simplest
    equivalent value comparisons.  A cond whose flags resolve through
    their single reaching defs in the jump's block (each flag's last
    def; all defs precede all jmps) compiles, and every def of a
    consumed flag var whose only use was the rewritten jump is
    dropped; everything else is the identity. *)
val compile_sub : sub term -> sub term

(** [compile_program prog]: [compile_sub] over every sub. *)
val compile_program : program term -> program term

(** [family_of_cond e]: the jcc family the cond belongs to ("je",
    "jne", "jl", "jle", "jg", "jge", "ja", "jae", "jb", "jbe"), or
    [None] when the cond is not a flag idiom the pass classifies. *)
val family_of_cond : exp -> string option
