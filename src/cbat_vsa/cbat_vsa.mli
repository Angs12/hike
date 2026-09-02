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

(* ARCH-1 — the tag-EXTRACTION module (the vsa_info producer's
   extraction half; the review's #1): the M6 classification walk over
   the converged solution, the kind arithmetic, the set-overlap
   merge, and the VLA idiom matcher.  The pass layer's
   [Convutils.vsa_kind] ALIASES [Cbat_extraction.kind] — one enum,
   no mapping layer. *)
module Cbat_extraction : sig
  (* The classification vocabulary — the pass layer's [vsa_kind] home
     (aliased there; [equal] derived here once). *)
  type kind =
    | Range of int64 * int64
    | Infinite of int64 * int64
    | Unbounded
    | Dead
    | VLA of Tid.t
  [@@deriving equal]

  (* [classify ?vla_tid ws]: Range / Infinite / Unbounded (top) / Dead
     (bottom) / VLA — the pure WordSet-to-kind function. *)
  val classify : ?vla_tid:tid -> WordSet.t -> kind option

  (* [bounds_of ws]: the signed (lo, hi) bounds, None when top/bottom. *)
  val bounds_of : WordSet.t -> (int64 * int64) option

  (* [k_range_of ws rsp_ws]: the ABI-visible k-range
     (k_min = addr_lo - rsp_hi, k_max = addr_hi - rsp_lo). *)
  val k_range_of : WordSet.t -> WordSet.t -> (int64 * int64) option

  (* [stack_address_of_rhs rhs]: the ADDRESS of a stack-access rhs
     (Load/Store, bare or under the lifter's pad-style Cast), None
     otherwise. *)
  val stack_address_of_rhs : Bil.exp -> Bil.exp option

  (* [st_tag_of ~tags blk addr' st_before]: the M6 tag-state meet
     (the address's free vars met with the block's IN-state values,
     the genuine-subset gate) — the ONE home of the meet discipline. *)
  val st_tag_of :
    tags:(tid, AI.t) Solution.t ->
    blk term -> exp -> AI.t -> AI.t

  (* [extract ~sp ~stack_access ~dynamic_alloc ~sol sub]: the per-def
     classification over the converged [sol] — the M6 walk, then the
     SET-OVERLAP MERGE.  The predicates are threaded as functions (the
     pass layer's relevance tags; no tag dependency here). *)
  val extract :
    sp:var ->
    stack_access:(def term -> bool) ->
    dynamic_alloc:(def term -> bool) ->
    sol:(tid, AI.t) Solution.t ->
    sub term ->
    kind Tid.Map.t * (int64 * int64) Tid.Map.t
    * (int64 * int64) Tid.Map.t

  (* [vla_decrement_p sp_base rhs]: the SHARED VLA idiom test (a
     non-literal `RSP := RSP - size` shape) — one fact, two roles. *)
  val vla_decrement_p : var -> Bil.exp -> bool

  (* [vla_size_of_rhs sp sub rhs]: the dynamic-allocation size
     expression — the `RSP := RSP - size` idiom, direct or indirect,
     or None.  The ONE home of the idiom matcher. *)
  val vla_size_of_rhs : var -> sub term -> Bil.exp -> Bil.exp option
end

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
