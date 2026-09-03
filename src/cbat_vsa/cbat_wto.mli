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

(* Bourdoncle weak topological ordering over plain accessors. *)

open Core_kernel
open Bap.Std

type comp =
  | Vertex of Tid.t
  | SCC of Tid.t * comp list

(* All blocks; heads precede members. *)
val flatten_comps : comp list -> Tid.t list

(* Heads of every nested SCC. *)
val heads_of_comps : comp list -> Tid.Set.t

(* One-line printer. *)
val pp_comp : Format.formatter -> comp -> unit

(* Recursive SCC partition. *)
val scc_partition :
  Tid.t list -> (Tid.t -> Tid.t list) -> (Tid.t -> Tid.t list) ->
  Tid.t list list

(* WTO; swapped accessors build the reversed ordering. *)
val wto :
  nodes:Tid.t list ->
  succ:(Tid.t -> Tid.t list) ->
  pred:(Tid.t -> Tid.t list) ->
  comp list
