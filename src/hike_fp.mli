(* The FP temp widths. *)
open Bap.Std

  val run_program :
    synth:Hike_synth.table -> program term -> Hike_synth.table * program term
