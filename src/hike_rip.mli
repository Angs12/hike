open Bap.Std

(** Rewrites each rip-tagged def's module-address literals ([is_address])
    into synthetic module addresses. Unclassified constants and store
    data retain their bits; the lifter tag is preserved.  The module
    addresses it mints are recorded in the returned table. *)
val prepare_program :
  synth:Hike_synth.table -> addr_bits:int -> is_address:(int64 -> bool) ->
  program term -> Hike_synth.table * program term

(** One block's RIP-tag rewrite; the table grows in place. *)
val prepare_block :
  synth:Hike_synth.table ref -> addr_bits:int ->
  is_address:(int64 -> bool) -> blk term -> blk term

(** Lets attribution finalize storage on the resolved values. Its named
    accesses receive byte indices; a copy-relocated [slots] address
    keeps its absolute form. *)
val resolve_with_layout :
  addr_bits:int -> slots:int64 list -> synth:Hike_synth.table ->
  layout:(synth:Hike_synth.table -> program term ->
          program term * Hike_synth_addr.region list * Hike_synth.table * 'a) ->
  program term -> program term * Hike_synth.table * 'a

(** Pure resolution with an already available component layout. *)
val resolve_program :
  ?slots:int64 list -> addr_bits:int -> synth:Hike_synth.table ->
  regions:Hike_synth_addr.region list -> program term ->
  Hike_synth.table * program term
