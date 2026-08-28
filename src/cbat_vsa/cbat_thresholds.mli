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

(* Cbat_thresholds — widening-threshold collection (docs/widening-thresholds-plan.md). One ladder per bitwidth per sub: the geometric default rungs ∪ the sub's program constants, deduped and sorted (unsigned ascending). *)

open Bap.Std

type t = (int * Word.t list) list

(* [collect sub]: the per-bitwidth rung ladders for one fixpoint run — geometric defaults ∪ the sub's program constants, deduped, sorted. Called once per [Cbat_vsa.static_graph_vsa] entry (each callee sub gets its own ladders). *)
val collect : sub term -> t
