(* Version-keyed walk memo; entries carry a stamped read-set. *)

#ifdef VSA_DEBUG
(* Hit accounting; compiled out of production by cppo. *)
val lookups : int ref
val hits : int ref
val stores : int ref
val stale : int ref
val empty_lookups : int ref
val reset_stats : unit -> unit
#endif

open Core_kernel
open Bap.Std

type value = Cbat_ai_representation.t

(* Stamped read-set plus value. *)
type entry = {
  e_reads : (Tid.t * int) list;
  e_value : value;
}

type t = entry Tid.Map.t Tid.Map.t

val empty : t

(* Value of a live entry, if any. *)
val find :
  version:(Tid.t -> int) -> t -> Tid.t -> Tid.t -> value option

(* Record a value with its read-set. *)
val add :
  version:(Tid.t -> int) ->
  t -> Tid.t -> Tid.t -> reads:Tid.Set.t -> value -> t
