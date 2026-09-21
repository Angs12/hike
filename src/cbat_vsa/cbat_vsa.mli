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

open Core
open Bap.Std
open Graphlib.Std

module WordSet = Cbat_clp_set_composite

module AI = Cbat_ai_representation

(* The one policy for what survives a call. *)
module Call_effects = Cbat_call_effects

(* Re-exported memory abstraction. *)
module Mem = Cbat_ai_memmap

(* Per-def classification over the converged solution. *)
module Cbat_extraction : sig
  (* Classification vocabulary: the (lo,hi) pair of the carrying
     constructors is the denotation's position interval on the model's
     ABSOLUTE segment line (the entry RSP = the segment base; a frame
     offset o sits at [stack_base + o]). *)
  type kind =
    | Range of int64 * int64
    | Infinite of int64 * int64
    | Caller of int64 * int64
    | Mixed of int64 * int64
    | Dead
  [@@deriving equal]

  (* The fully-infinite span (the whole position line) — the kind of a
     TOP denotation. *)
  val unbounded_span : kind

  val is_unbounded_span : int64 -> int64 -> bool

  (* Kind of a word set (the denotation, read in place). *)
  val classify : WordSet.t -> kind

  (* The split over ABSOLUTE positions: entirely at/above the
     entry RSP -> [Caller]; entirely below -> [Range]; two-sided or
     wrapped -> [Mixed]. *)
  val caller_split : kind -> kind

  (* The absolute position of a frame offset (the segment base + the
     offset, overflow-checked). *)
  val position_of_offset : int64 -> int64 option

  (* Address of a stack-access rhs, if any. *)
  val stack_address_of_rhs : Bil.exp -> Bil.exp option

end

(* Re-exported profiling interface. *)
module Stages = Cbat_vsa_stages


type vsa_sol = (tid, AI.t) Solution.t

(* Solution still changing at the step cap. *)
exception Fixpoint_not_converged of int * (tid, AI.t) Solution.t
  * (tid * tid) option

(* Set the address width in bits. *)
val set_addr_bits : int -> unit

(* An image-backed section: the span's inclusive bounds plus the
   section's static content. *)
type section_image = Cbat_transfer.section_image = {
  img_lo : int64;
  img_hi : int64;
  img_bytes : Bytes.t;
}

(* Threads the image-backed sections in: only sections whose runtime
   content IS the static image — never relocated, never written. *)
val set_section_images : section_image list -> unit
val with_images : section_image list -> (unit -> 'a) -> 'a

val init_sol : abi:Hike_abi.t -> ?entry:AI.t ->  sub term -> vsa_sol

val static_graph_vsa :
  abi:Hike_abi.t ->
  ?written:Var.Set.t option Tid.Map.t ->
  ?resolved:Tid.Set.t Tid.Map.t ->
  ?sub_lookup:(int64 -> Tid.t option) ->
  Program.t -> Sub.t -> vsa_sol -> vsa_sol

(* The SOLVE's own replay — for Hike_cfg_complete, the producer's
   completion loop, ONLY.  Consumers use the seam [denote_exp_at];
   this is a raw replay from the given state. *)
val solve_denote :
  pre:AI.t -> blk:blk term -> ?def:def term -> exp ->
  (WordSet.t, Type.error) Result.t

(* The word-set denotation of an exp in a given env — the vocabulary
   of the completion loop's own folds. *)
val denote_imm_exp : exp -> AI.t -> (WordSet.t, Type.error) Result.t

(* One replay per block: the block's defs fold [denote_def] from the
   solution's entry state and [f] folds over each def's (before, after)
   states.  The completion's per-def queries ride this fold — one
   replay per block, never one per def. *)
val fold_block_states :
  sol:(tid, AI.t) Solution.t ->
  blk term ->
  init:'acc ->
  f:(AI.t -> AI.t -> def term -> 'acc -> 'acc) ->
  'acc * AI.t

(* [e] denotes in the before-env of [def] — the Env Tag the solve
   stamped on the def, or [AI.top] when the def carries no tag (minted
   after the analysis boundary) — or, with no [def], in the block's
   postcondition.  [pre] feeds the VSA_DEBUG differential's replay
   only. *)
val denote_exp_at :
  ?post:AI.t ->
  pre:AI.t -> blk:blk term -> ?def:def term -> exp ->
  (WordSet.t, Type.error) Result.t



(* The Env Tag: the before-state environment the solve held at a def,
   riding the def's value.  Absence means the def is outside the
   analysis boundary — minted after it, or its sub did not converge —
   and denotes TOP. *)
val env_tag : def term -> AI.t option

val set_env_tag : AI.t -> def term -> def term

(* The solve's boundary sweep: one (pre, post) env pair per block (pre
   the solution's entry state, post the block's def replay from it) and
   the sub with every def stamped with its before-state. *)
val stamp_envs_of_sol :
  sol:vsa_sol -> sub term -> (AI.t * AI.t) Tid.Map.t * sub term

(* The block's last def per lhs var (the reaching def at the block's
   end). *)
val last_defs : blk term -> def term Var.Map.t

(* The fixtures' construction seam: consumed by test_cbat and the
   probes, never by production src/. *)
module Test_seam : sig
  val denote_def : def term -> AI.t -> AI.t

  val denote_defs : blk term -> AI.t -> AI.t

  val denote_imm_exp : exp -> AI.t -> (WordSet.t, Type.error) Result.t

  (* One per-block state replay: the block's defs fold [denote_def]
     from its solution entry state; [f] folds over each def's (before,
     after) states. *)
  val fold_block_states :
    sol:(tid, AI.t) Solution.t ->
    blk term ->
    init:'acc ->
    f:(AI.t -> AI.t -> def term -> 'acc -> 'acc) ->
    'acc * AI.t

  val reachable_jumps : AI.t -> jmp term seq -> jmp term seq

  (* Constrain a state by an edge's cond. *)
  val constrain_edge :
    env:AI.t -> ?landmarks:Cbat_landmarks.t -> exp -> AI.t

  (* The inverse denote: one backward rule per node kind, the mirror of
     the forward transfer — env + expression + the constraint the value
     must satisfy -> the refined env. *)
  val inverse_denote : env:AI.t -> ?cells:Cbat_backward.pending_cell list ref -> ?nonneg:(exp -> bool) -> ?landmarks:Cbat_landmarks.t -> exp -> WordSet.t -> AI.t

  (* One fixpoint run's context: the static per-block facts, the
     convention facts, and the run's mutable state. *)
  type refine_ctx

  (* The per-run context (the walk fixtures' construction seam). *)
  val mk_rctx : cfg:Graphs.Tid.t -> abi:Hike_abi.t -> sub term -> refine_ctx

  (* The deep backward walk: the env threads through every visited
     block's defs, running to its fixpoint over the block; [seeds] are
     the cond's leaf constraints. *)
  val refine_edge :
    sol:(tid, AI.t) Solution.t ->
    rctx:refine_ctx ->
    seeds:(var * WordSet.t) list ->
    AI.t -> blk term -> AI.t
end
