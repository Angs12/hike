open Bap.Std

(** Resolve tagged addresses, then let attribution finalize
    storage on the resolved values. Its named accesses receive byte
    indices; a copy-relocated [slots] address keeps its absolute form.
    Unclassified constants retain their bits; the lifter tag is
    preserved. *)
val resolve_with_layout :
  addr_bits:int -> is_address:(int64 -> bool) -> slots:int64 list ->
  layout:(synth:Hike_synth.table -> program term ->
          program term * Hike_synth_addr.region list * 'a) ->
  program term -> program term * 'a

(** Pure resolution with an already available component layout. *)
val resolve_program :
  ?slots:int64 list -> addr_bits:int -> is_address:(int64 -> bool) ->
  regions:Hike_synth_addr.region list -> program term -> program term
