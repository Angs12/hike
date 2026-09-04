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

(* Whole-map memo keyed by block; one map per block is retained. *)
module Block_map (V : Value) : sig
  type value = V.t

  (* Stored version plus the whole definition-to-value map. *)
  type entry = {
    e_ver : int;
    e_map : value Tid.Map.t;
  }

  type t = entry Tid.Map.t

  val empty : t

  (* Map of a block whose stored version still matches. *)
  val find :
    version:(Tid.t -> int) -> t -> Tid.t -> value Tid.Map.t option

  (* Store a block's map, replacing any older version. *)
  val add : t -> Tid.t -> ver:int -> value Tid.Map.t -> t
end
