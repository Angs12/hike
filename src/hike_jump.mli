open Bap.Std
open Bap_core_theory

(** [compile_sub target sub] rewrites jcc flag idioms into the simplest
    equivalent value comparisons; flags are the vars [target] registers for
    the core-theory flag roles.  A cond whose flags do not resolve through
    their single reaching defs is unchanged; every def of a consumed flag
    var whose only use was the rewritten jump is dropped. *)
val compile_sub : Theory.Target.t -> sub term -> sub term
