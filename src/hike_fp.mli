(* The FP temp widths. *)
open Bap.Std

  val run_program :
    word_bits:int ->
    synth:Hike_synth.table -> program term -> Hike_synth.table * program term

  (** One block's FP qualification; the table grows in place. *)
  val run_block :
    word_bits:int ->
    synth:Hike_synth.table ref -> blk term -> blk term
