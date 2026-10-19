(* The transfer-target vocabulary: the memory slot an indirect transfer
   reads its destination through. *)
open Bap.Std

(* The sub's definitions and phis, built once so a loop resolving many
   targets for one sub shares the scan. *)
type index

val index_of_sub : sub term -> index

(* The linker slot the transfer's target reads, if any: a target that
   is (or resolves through the sub's defs to) a load from a constant
   address names that address.  [origin] maps a storage base var to its
   module byte origin, so a resolved component-relative access recovers
   its absolute slot.  [index] shares one per-sub def scan; without it
   (and with [sub]) each call builds its own. *)
val slot_of_target :
  ?index:index -> synth:Hike_synth.table -> ?origin:(var -> int64 option) ->
  ?sub:sub term -> exp -> int64 option
