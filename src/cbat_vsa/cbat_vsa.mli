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

(* Re-exported memory abstraction. *)
module Mem = Cbat_ai_memmap

(* Per-def classification over the converged solution. *)
module Cbat_extraction : sig
  (* Classification vocabulary. *)
  type kind =
    | Range of int64 * int64
    | Infinite of int64 * int64
    | Unbounded
    | Dead
    | VLA of Tid.t
  [@@deriving equal]

  (* Kind of a word set. *)
  val classify : ?vla_tid:tid -> WordSet.t -> kind option

  (* Signed bounds; None when top/bottom. *)
  val bounds_of : WordSet.t -> (int64 * int64) option

  (* ABI-visible k-range. *)
  val k_range_of : WordSet.t -> WordSet.t -> (int64 * int64) option

  (* Address of a stack-access rhs, if any. *)
  val stack_address_of_rhs : Bil.exp -> Bil.exp option

  (* Value-based stack address predicate (frame term in state). *)
  val is_seed : AI.t -> exp -> bool

  (* Tag-state meet for one address. *)
  val st_tag_of :
    tags:(tid, AI.t) Solution.t ->
    blk term -> exp -> AI.t -> AI.t

  (* Per-def classification over [sol]; the two-channel frame-residency
     proof (spec §2.2) seeds accesses, replacing the deleted tag match. *)
  val extract :
    sp:var ->
    dynamic_alloc:(def term -> bool) ->
    alloc_tids:Tid.Set.t ->
    sol:(tid, AI.t) Solution.t ->
    sub term ->
    kind Tid.Map.t * (int64 * int64) Tid.Map.t

  (* True for a non-literal [RSP := RSP - size]. *)
  val vla_decrement_p : var -> Bil.exp -> bool

  (* Size expression of a dynamic allocation, if any. Takes the sub's
     lhs-indexed defs; the caller builds it once. *)
  val vla_size_of_rhs : var -> def term Var.Map.t -> Bil.exp -> Bil.exp option

  (* Runtime-sized SP decrements (spec §2.3). *)
  val detect_dynamic_alloc : var -> sub term -> Tid.Set.t
end

(* Re-exported profiling interface. *)
module Stages = Cbat_vsa_stages


type vsa_sol = (tid, AI.t) Solution.t

(* Solution still changing at the step cap. *)
exception Fixpoint_not_converged of int * (tid, AI.t) Solution.t
  * (tid * tid) option

(* Opaque frame relation; None is bottom. *)
type frame

(* Set the address width in bits. *)
val set_addr_bits : int -> unit

(* Frame relation of a state. *)
val frame_of_state : AI.t -> frame option


(* Rewrite an address to its offset expression. *)
val rewrite_addr : frame option -> exp -> exp

val denote_def : def term -> AI.t -> AI.t

val denote_defs : blk term -> AI.t -> AI.t

val denote_imm_exp : exp -> AI.t -> (WordSet.t, Type.error) Result.t

val reachable_jumps : AI.t -> jmp term seq -> jmp term seq

(* Refine a state by a taken jump condition. *)
val assume_jump_cond :
  ?defs:(def term * bool) Var.Map.t ->
  ?flag_state:(var * Bil.binop * exp * word) option ->
  AI.t -> jmp term -> AI.t

(* Meet a cell with a trace-exact constraint. *)
val constrain_cell_on_trace : st:AI.t -> live:WordSet.t Var.Map.t -> AI.t ->
  mem:exp -> addr:exp -> size:Size.t -> endian:endian -> WordSet.t -> AI.t

(* Leaf constraints of a guard. *)
type analysis_ctx = {
  defs : (def term * bool) Var.Map.t option;
  stores : def term list option;
  flag_state : (var * Bil.binop * exp * word) option;
  has_sub : bool;
}

type edge_constraint =
  | Var of var * WordSet.t
  | Cell of exp * exp * Size.t * endian * WordSet.t
  | Infeasible

val edge_constraints : env:AI.t -> ?ctx:analysis_ctx -> exp -> WordSet.t -> edge_constraint list

(* The live-constraint map the backward walk propagates. *)
module Live : sig
  type t = WordSet.t Var.Map.t
end

(* Run context of one fixpoint run: per-block facts, the memos, the shared
   per-SCC walk budget. Abstract; built by [mk_rctx], read by [walk_budget]. *)
type refine_ctx

(* The per-run context (the walk fixtures' construction seam). *)
val mk_rctx : cfg:Graphs.Tid.t -> sub term -> refine_ctx

(* The shared per-SCC walk-pop budget cell (the binding-regime seam). *)
val walk_budget : refine_ctx -> int ref

(* Candidate-1 overlap census record. In production builds the dump is
   always empty (nothing is compiled in); vsa-debug builds accumulate
   one record per executed backward walk. *)
type walk_record = {
  wr_guard : tid;
  wr_jmp : tid;
  wr_seq : int;
  wr_nvar : int;
  wr_ncell : int;
  wr_reads : Tid.Set.t;
}

val walk_records_reset : unit -> unit
val walk_records_dump : unit -> walk_record list

(* The deep backward walk: refines [env] by an edge's seed constraints,
   bounded by [steps] (None = the 256 cap). Budget-limited walks spend the
   shared cell; the live solution is the walk's internal propagation
   record (both callers discard it). *)
val refine_edge :
  sol:(tid, AI.t) Solution.t ->
  rctx:refine_ctx ->
  ?defs:(def term * bool) Var.Map.t option ->
  ?reads:Tid.Set.t ref option ->
  ?steps:int option ->
  AI.t -> blk term -> edge_constraint list -> AI.t * (tid, Live.t) Solution.t

val init_sol : ?entry:AI.t ->  sub term -> vsa_sol

(* Per-sub def-chain map. *)
val defs_of_sub : sub term -> (def term * bool) Var.Map.t
val stores_of_sub : sub term -> def term list

val static_graph_vsa : tid list -> Program.t -> Sub.t -> vsa_sol -> vsa_sol
