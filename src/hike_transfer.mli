(* The transfer-target vocabulary: the memory slot an indirect transfer
   reads its destination through. *)
open Bap.Std

(* The linker slot the transfer's target reads, if any: a target that
   is (or resolves through the sub's defs to) a load from a constant
   address names that address. *)
val slot_of_target : ?sub:sub term -> exp -> int64 option
