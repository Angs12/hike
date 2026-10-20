(* The FP temp widths. *)
open Bap.Std

  val run_program :
    synth:Hike_synth.table -> program term -> Hike_synth.table * program term

  (** One block's FP qualification; the table grows in place. *)
  val run_block :
    synth:Hike_synth.table ref -> blk term -> blk term
