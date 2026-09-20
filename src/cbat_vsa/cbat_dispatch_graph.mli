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

(* The engine's dispatch graph: the CFG plus the Resolved dispatches'
   extra successor edges.  One succs/preds pair serves the WTO, the
   worklist, and the per-block predecessor lists. *)

open Core
open Bap.Std
open Graphlib.Std

type t = {
  succs : tid -> tid list;
  preds : tid -> tid list;
  (* The extra edges' targets: the blocks that GAINED a predecessor.
     The worklist seeds them directly — a warm seed's stable prefix
     never enqueues them (propagation is change-driven). *)
  gained_preds : Tid.Set.t;
}

(* The graph over [cfg] for [sub]: each jmp's [resolved] target set
   (a plain argument — empty map adds no edges) contributes extra
   successor edges for the jmp's block, filtered to [blocks]; the
   mirrors land in the target's predecessor list, deduplicated. *)
val make :
  cfg:Graphs.Tid.t ->
  blocks:Tid.Set.t ->
  Tid.Set.t Tid.Map.t ->
  sub term ->
  t
