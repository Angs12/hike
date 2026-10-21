(* Post-SSA dead-code elimination: remove unread target-flag and virtual
   temporaries. *)

open Bap.Std
open Bap_core_theory

val dce_sub :
  synth:Hike_synth.table -> target:Theory.Target.t -> sub term -> sub term


(** The post-Finalize variant: candidates only in [blocks], use counts
    over the whole sub.  Existing blocks stay untouched. *)
val dce_blocks :
  synth:Hike_synth.table -> target:Theory.Target.t -> blocks:Tid.Set.t ->
  sub term -> sub term
