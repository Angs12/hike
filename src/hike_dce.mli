(* Post-SSA dead-code elimination: remove unread target-flag and virtual
   temporaries. *)

open Bap.Std
open Bap_core_theory

val dce_sub :
  synth:Hike_synth.table -> target:Theory.Target.t -> sub term -> sub term
