open Bap.Std
open Bap_core_theory

(** [compile_sub ?file target sub] rewrites every jump's cond into the
    simplest equivalent flag-free expression: the defs of its block, and
    of a unique goto predecessor chain, are substituted backward and
    simplified.  An indirect transfer's edges are the destinations
    discovery provided on its instruction in [file]'s package (none
    without [file]).  Flags are the vars [target] registers for the
    core-theory flag roles.  A cond with no flag-free form is unchanged;
    every def of a consumed flag var no read survives is dropped. *)
val compile_sub : ?file:string -> Theory.Target.t -> sub term -> sub term
