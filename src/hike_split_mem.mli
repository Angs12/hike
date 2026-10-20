(* Node fission. *)
open Bap.Std


  val split_sub : synth:Hike_synth.table ref -> sub term -> sub term

(** One block's split; identity when no def needs it. *)
val split_block : synth:Hike_synth.table ref -> blk term -> blk term
  val normalize :
    synth:Hike_synth.table -> program term -> Hike_synth.table * program term
