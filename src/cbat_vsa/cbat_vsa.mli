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

(* The per-def runtime origin: the origin the solve computed for the
   def's value, stamped at the solve boundary.  [None] = outside the
   analysis boundary (reads Abs). *)
module Def_origin : sig
  val def_origin : def term -> Hike_origin.t option
  val with_origin : Hike_origin.t -> def term -> def term
end

(* Re-exported profiling interface. *)
module Stages = Cbat_vsa_stages

(* The KB operation census (compiled only under VSA_DEBUG). *)
#ifdef VSA_DEBUG
module Cbat_kb_census : sig
  val bump : string -> unit
end

(* The attribution census (compiled only under VSA_DEBUG). *)
module Cbat_attr_census : sig
  val bump : string -> unit
end
#endif


type vsa_sol = (tid, AI.t) Solution.t

(* Solution still changing at the step cap. *)
exception Fixpoint_not_converged of int * (tid, AI.t) Solution.t

(* Set the address width in bits. *)
val set_addr_bits : int -> unit

(* Set the SP var the VLA rebase anchors on. *)
val set_sp_var : var -> unit

(* An image-backed section: the span's inclusive bounds plus the
   section's static content; [img_slots] are the linker-owned slot
   addresses in the span — a slot's value the loader writes, so the
   file bytes there are not a value. *)
type section_image = Cbat_transfer.section_image = {
  img_lo : int64;
  img_hi : int64;
  img_bytes : Bytes.t;
  img_slots : Int64.Set.t;
}

(* Threads the image-backed sections in: only sections whose runtime
   content IS the static image — never relocated, never written. *)
val set_section_images : section_image list -> unit
val with_images : section_image list -> (unit -> 'a) -> 'a

val init_sol : abi:Hike_abi.t -> ?entry:AI.t -> sub term -> vsa_sol

(* The D1 VLA-event predicate: a non-singleton, strictly descending SP
   move opens a frame; the extent is the seed's own fact. *)
val vla_event :
  before:WordSet.t -> after:WordSet.t -> Hike_origin.vla_extent option

(* The sub's entry block: the CFG's [Start] pseudo-node points to it. *)
val entry_block_of : sub term -> blk term option

(* The round-down idiom normalization: the two-def [(x >> k) << k]
   pair becomes the mask AND + identity copy. *)
val normalize_round : Sub.t -> Sub.t

val static_graph_vsa :
  abi:Hike_abi.t ->
  def_reads:(def term -> Var.Set.t) ->
  def_writes:(def term -> Var.Set.t) ->
  phi_reads:(phi term -> Var.Set.t) ->
  phi_writes:(phi term -> Var.Set.t) ->
  jmp_reads:(jmp term -> Var.Set.t) ->
  ?written:Core.Int.Set.t option Tid.Map.t ->
  ?resolved:Tid.Set.t Tid.Map.t ->
  ?sub_lookup:(int64 -> Tid.t option) ->
  Sub.t -> vsa_sol -> vsa_sol

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
  val mem_addr_of : exp -> exp option

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

  (* Constrain a state by an edge's cond (the context's landmark table). *)
  val constrain_edge :
    env:AI.t -> landmarks:Cbat_landmarks.t -> exp -> AI.t

  (* One backward rule per node kind, the mirror of the forward transfer —
     the forward transfer — env + expression + the constraint the value
     must satisfy -> the refined env. *)
  val constrain_operands : env:AI.t -> ?cells:Cbat_backward.pending list ref -> ?nonneg:(exp -> bool) -> landmarks:Cbat_landmarks.t -> exp -> WordSet.t -> AI.t

  (* One fixpoint run's context: the static per-block facts, the
     convention facts, and the run's mutable state. *)
  type refine_ctx

  (* The per-run context: the library builder with production's own
     defaults — the non-negativity oracle, the run's sub-address lookup,
     and one landmark table. *)
  val normalize_round : Sub.t -> Sub.t
  val mk_rctx :
    abi:Hike_abi.t ->
    def_reads:(def term -> Var.Set.t) ->
    def_writes:(def term -> Var.Set.t) ->
    phi_reads:(phi term -> Var.Set.t) ->
    phi_writes:(phi term -> Var.Set.t) ->
    jmp_reads:(jmp term -> Var.Set.t) ->
    ?sub_lookup:(int64 -> Tid.t option) -> sub term -> refine_ctx

  (* The context's landmark table (one source of truth). *)
  val landmarks_of : refine_ctx -> Cbat_landmarks.t

  (* Run [f] with the context's table widening at [head]. *)
  val with_widening_head :
    refine_ctx -> Tid.t option -> (unit -> 'a) -> 'a

  (* The deep backward walk: the env threads through every visited
     block's defs, running to its fixpoint over the block; [seeds] are
     the cond's constrained vars. *)
  val refine_edge :
    sol:(tid, AI.t) Solution.t ->
    rctx:refine_ctx ->
    seeds:Var.Set.t ->
    AI.t -> blk term -> AI.t

  (* The walk's env-write sites, named for the counting refine. *)
  type write_site = Cbat_backward.write_site = Output_write | Input_write

  (* The walked env with the per-site count of ACTUAL env writes — a
     delivery equal to the state's value writes nothing, so it never
     counts. *)
  val refine_edge_count_writes :
    sol:(tid, AI.t) Solution.t ->
    rctx:refine_ctx ->
    seeds:Var.Set.t ->
    AI.t -> blk term -> AI.t * int * int

end
