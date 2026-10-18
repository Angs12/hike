(* Node fission. *)
open Bap.Std


  val split_sub : synth:Hike_synth.table ref -> sub term -> sub term
  val normalize :
    synth:Hike_synth.table -> program term -> Hike_synth.table * program term
