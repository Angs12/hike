open Bap.Std
open Bap.Std.Bil.Types

(* The variadic stamp: the emitter defines a stamped sub as a real LLVM
   variadic. *)
val is_variadic : sub term -> bool

(* The pass: stamps every non-fixed-signature sub whose body holds the
   construction. *)
val stamp :
  abi:Hike_abi.t ->
  entry:int64 ->
  denote:(blk:blk term -> ?def:def term -> exp ->
           (Cbat_clp_set_composite.t, Type.error) Result.t) ->
  program term ->
  program term
