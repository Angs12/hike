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

open Core_kernel
open Bap.Std
open Graphlib.Std

module WordSet = Cbat_clp_set_composite

module AI = Cbat_ai_representation

(* Hike port fix (Phase 2): re-export the memory abstraction alongside [AI] so the wrapped library exposes it under the main module (the sibling modules are only reachable through dune's generated [Cbat_vsa__] wrapper otherwise). *)
module Mem = Cbat_ai_memmap

(* The per-stage profiling interface (the Q6 harness) — re-exported so the
   debug probes can read the counters. Production links the NO-OP adapter
   ([cbat_vsa_stages_prod.ml]), so [Stages.enabled = false] and every
   [Stages.time] is the identity there; only the vsa-debug profile links
   the timing adapter. See src/cbat_vsa/dune and AGENTS.md §6. *)
module Stages = Cbat_vsa_stages


type vsa_sol = (tid, AI.t) Solution.t

(* Raised by [static_graph_vsa] when the fixpoint's verification round finds the solution still changing at the [~steps] cap — the solution would be an under-approximation and must not feed the narrow-tag decisions (see. *)
exception Fixpoint_not_converged of int * (tid, AI.t) Solution.t
  * (tid * tid) option

(* [frame]: one state's frame relation (opaque) — the frame-derived registers with their offset-from-origin expressions, carried IN the abstract state (the in-state port; see [AI.frame_of]/[AI.set_frame]). None = the vacuous bottom state (the join identity). *)
type frame

(* [set_addr_bits n]: the program architecture's address size in bits (the Target-derived width, O1) — the memmap's native key width. Set at pass setup (hike.ml); 0/unset = the BIL type's size is the fallback (unit tests). *)
val set_addr_bits : int -> unit

(* [frame_of_state env]: the state's frame relation (None = the vacuous bottom state) — read by consumers that mirror the fixpoint's address rewrite (e.g. the precision probe's classification). *)
val frame_of_state : AI.t -> frame option


(* [rewrite_addr frame a]: normalize a frame-derived Load/Store address to its offset-from-origin expression; [a] unchanged when no fact applies. *)
val rewrite_addr : frame option -> exp -> exp

val denote_def : def term -> AI.t -> AI.t

val denote_defs : blk term -> AI.t -> AI.t

val denote_imm_exp : exp -> AI.t -> (WordSet.t, Type.error) Result.t

val reachable_jumps : AI.t -> jmp term seq -> jmp term seq

(* Branch-assume refinement of the state on a taken edge by the jump's condition (exported for the unit tests). *)
val assume_jump_cond : ?refineable:Var.Set.t ->
  ?defs:(def term * bool) Var.Map.t ->
  ?flag_state:(var * Bil.binop * exp * word) option ->
  AI.t -> jmp term -> AI.t

(* [constrain_cell_on_trace ~st ~live env ~mem ~addr ~size ~endian cstr]: the TRACE-EXACT cell meet (the trace-partitioning design, docs/trace-partitioning-plan.md §3): the address's value-set on the trace = the frame-rewritten address denoted with the load's block state [st] intersected. *)
val constrain_cell_on_trace : st:AI.t -> live:WordSet.t Var.Map.t -> AI.t ->
  mem:exp -> addr:exp -> size:Size.t -> endian:endian -> WordSet.t -> AI.t

(* the edge-constraint collector (the trace-partitioning design, docs/trace-partitioning-plan.md §3): the PURE constraint derivation — the guard's edge constraint decomposed into the leaf constraints for the backward walk. TOTAL: every shape has a row (the NO-FALLBACK doctrine). *)
type analysis_ctx = {
  refineable : Var.Set.t option;
  defs : (def term * bool) Var.Map.t option;
  stores : def term list option;
  flag_state : (var * Bil.binop * exp * word) option;
  sub : sub term option;
  blk : blk term option;
}

type edge_constraint =
  | Var of var * WordSet.t
  | Cell of exp * exp * Size.t * endian * WordSet.t
  | Infeasible

val edge_constraints : env:AI.t -> ?ctx:analysis_ctx -> exp -> WordSet.t -> edge_constraint list

val init_sol : ?entry:AI.t ->  sub term -> vsa_sol

(* the per-sub def-chain map (base -> the LAST def + the single-def flag) — the backward walk's def table. *)
val defs_of_sub : sub term -> (def term * bool) Var.Map.t
val stores_of_sub : sub term -> def term list

val static_graph_vsa : tid list -> Program.t -> Sub.t -> vsa_sol -> vsa_sol
