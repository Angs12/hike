(* The VSA: the pausable fused solve and the def-origin stamp — the
   producer's public surface. *)
open Bap.Std
open Bap_core_theory

  (** Arms the classifier's address width.  Analysis entries self-arm;
    probes may set it directly before a standalone solve. *)
  val set_addr_bits : int -> unit

  (** The per-def runtime origin: the origin the solve computed for
    the def's value, stamped at the solve boundary.  [None] = outside
    the analysis boundary (reads no origin). *)
  module Def_origin : sig
    val def_origin : def term -> Hike_origin.t option
    val with_origin : Hike_origin.t -> def term -> def term
  end

  (** An image-backed section: inclusive bounds plus static content;
      [img_slots] are the linker-owned slot addresses in the span. *)
  type section_image = Cbat_vsa.section_image = {
    img_lo : int64;
    img_hi : int64;
    img_bytes : Bytes.t;
    img_slots : Core.Int64.Set.t;
  }

  type lookup_fn = int64 -> Tid.t option

  (** The solver retains the matching body, seed and wake set until resume. *)
  type paused

  (** The callees whose final summaries this solve needs. *)
  val blocked : paused -> Tid.Set.t

  (** The canonical body and its seed stay paired across decoder growth. *)
  type continuation = private {
    canonical : sub term;
    seed : Cbat_vsa.vsa_sol;
  }

  type completed = {
    envs : (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t;
    sub : sub term;
    block_addrs : Tid.t Addr.Map.t;
    synth : Hike_synth.table;
    continuation : continuation;
  }

  type outcome = Done of completed | Paused of paused

  (** The fused solve under [callee]: phases of solve + resolution
      growth, pausing when a reachable call's callee is [Blocked]. *)
  val start :
    Theory.Target.t ->
    lookup:lookup_fn ->
    images:section_image list ->
    callee:(Tid.t -> Cbat_vsa.Call_effects.callee) ->
    block_addrs:Tid.t Addr.Map.t ->
    synth:Hike_synth.table ->
    foreign_slots:Core.Int64.Set.t ->
    sub term ->
    outcome

  (** Continues a completed solve after incremental SSA/decode growth. *)
  val restart :
    Theory.Target.t -> lookup:lookup_fn -> images:section_image list ->
    callee:(Tid.t -> Cbat_vsa.Call_effects.callee) ->
    block_addrs:Tid.t Addr.Map.t -> synth:Hike_synth.table ->
    foreign_slots:Core.Int64.Set.t ->
    previous:continuation -> woken:Tid.Set.t ->
    sub term -> outcome

  (** Continues a paused solve from its seed under the new [callee]. *)
  val resume :
    Theory.Target.t ->
    lookup:lookup_fn ->
    images:section_image list ->
    callee:(Tid.t -> Cbat_vsa.Call_effects.callee) ->
    foreign_slots:Core.Int64.Set.t ->
    paused ->
    outcome

  (** The persistent registers a sub's defs write (partial defs at
      their base register). *)
  val written_regs_of_sub : synth:Hike_synth.table -> sub term -> Var.Set.t
