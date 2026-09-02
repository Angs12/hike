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

(* The BOURDONCLE WEAK TOPOLOGICAL ORDERING interface (architecture
   review #5).  Accessor-polymorphic: plain [Tid.t] node lists and
   edge-accessor functions — NO BAP graph type here.  [Cbat_wto.wto_
   of_cfg] (in [cbat_vsa.ml]) is the Graphs adapter; the REVERSED
   ordering is [wto ~succ:preds ~pred:succs] (the accessors swapped —
   a call-shape, not a copy).  See [cbat_wto.ml]'s header for the
   algorithm and the Theorem-3/5 roles of [heads_of_comps]/the
   component tree. *)

open Core_kernel
open Bap.Std

type comp =
  | Vertex of Tid.t
  | SCC of Tid.t * comp list

(* Every block in the ordering (head before its component's members). *)
val flatten_comps : comp list -> Tid.t list

(* The heads of every nested SCC — Theorem 3's minimal admissible
   widening-point set. *)
val heads_of_comps : comp list -> Tid.Set.t

(* The one-line pretty printer (the "(h inner...)" form). *)
val pp_comp : Format.formatter -> comp -> unit

(* The recursive SCC partition (Kosaraju shape) — exported for the
   direct tests. *)
val scc_partition :
  Tid.t list -> (Tid.t -> Tid.t list) -> (Tid.t -> Tid.t list) ->
  Tid.t list list

(* The weak topological ordering over plain accessors.  [nodes] fixes
   the traversal seed order (hence the head choice); swapped accessors
   build the reversed ordering. *)
val wto :
  nodes:Tid.t list ->
  succ:(Tid.t -> Tid.t list) ->
  pred:(Tid.t -> Tid.t list) ->
  comp list
