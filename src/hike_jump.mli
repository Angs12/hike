open Bap.Std
open Bap_core_theory

(** [compile_sub target sub] rewrites every jump's cond into the simplest
    equivalent flag-free expression: the defs of its block, and of a unique
    goto predecessor chain, are substituted backward and simplified.  The
    walk reads the BIR's edges: a resolved dispatch's arms are direct
    gotos.  Flags are the vars [target] registers for the core-theory flag
    roles.  A cond with no flag-free form is unchanged; every def of a
    consumed flag var no read survives is dropped.  The comparison defs
    it binds are recorded in the returned table. *)
val compile_sub :
  synth:Hike_synth.table -> Theory.Target.t -> sub term ->
  Hike_synth.table * sub term
