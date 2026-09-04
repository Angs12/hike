(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

(* Version-keyed memo; entries carry a stamped read-set. *)

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

module type Value = sig
  type t
end

module Make (V : Value) : sig
  type value = V.t

  (* Stamped read-set plus value. *)
  type entry = {
    e_reads : (Tid.t * int) list;
    e_value : value;
  }

  type t = entry Tid.Map.t Tid.Map.t

  val empty : t

  (* True when no recorded block changed state. *)
  val valid : version:(Tid.t -> int) -> entry -> bool

  (* Stamp a finished computation's read-set. *)
  val stamp : version:(Tid.t -> int) -> Tid.Set.t -> (Tid.t * int) list

  (* Value of a live entry, if any. *)
  val find :
    version:(Tid.t -> int) -> t -> Tid.t -> Tid.t -> value option

  (* Record a value with its read-set. *)
  val add :
    version:(Tid.t -> int) ->
    t -> Tid.t -> Tid.t -> reads:Tid.Set.t -> value -> t
end
