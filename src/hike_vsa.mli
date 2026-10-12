(* The VSA: the pausable fused solve and the def-origin stamp — the
   producer's public surface. *)
open Bap.Std
open Bap_core_theory

  (** Arms the classifier's address width.  Analysis entries self-arm;
    probes may set it directly before a standalone solve. *)
  val set_addr_bits : int -> unit

  (** The per-def runtime origin: the origin the solve computed for
    the def's value, stamped at the solve boundary.  [None] = outside
    the analysis boundary (reads [Abs]). *)
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

  (** A solve paused on callees with no summary yet: [p_seed] is the
      phase's solution (every blocked call's continuation bottom),
      [p_blocked] the callees it waits on. *)
  type paused = {
    p_sub : sub term;
    p_resolved : Tid.Set.t Tid.Map.t;
    p_block_addrs : Tid.t Addr.Map.t;
    p_seed : Cbat_vsa.vsa_sol;
    p_blocked : Tid.Set.t;
  }

  (** A solve's end: the per-block (pre, post) environments, the
      rewritten sub and the grown block-address map, or a pause. *)
  type outcome =
    | Done of (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t * sub term * Tid.t Addr.Map.t
    | Paused of paused

  (** The fused solve under [callee]: phases of solve + resolution
      growth, pausing when a reachable call's callee is [Blocked]. *)
  val start :
    Theory.Target.t ->
    lookup:lookup_fn ->
    images:section_image list ->
    callee:(Tid.t -> Cbat_vsa.Call_effects.callee) ->
    block_addrs:Tid.t Addr.Map.t ->
    foreign_slots:Core.Int64.Set.t ->
    sub term ->
    outcome

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
  val written_regs_of_sub : sub term -> Var.Set.t
