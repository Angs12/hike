(* The jump compiler (construction).  Exposes the BIR rewrite
   only: pipeline registration is the slot-window phase. *)

open Bap.Std
open Bap_core_theory

(** [compile_sub target sub]: rewrites jcc flag idioms into the
    simplest equivalent value comparisons.  The flags are the vars
    [target] registers for the core-theory flag roles (zero, carry,
    sign, overflow), compared by [Var.same].  A cond whose flags
    resolve through their single reaching defs (the jump's block's last
    defs, or the unique reaching definitions at the block entry)
    compiles, and every def of a consumed flag var whose only use was
    the rewritten jump is dropped; everything else is the identity. *)
val compile_sub : Theory.Target.t -> sub term -> sub term
