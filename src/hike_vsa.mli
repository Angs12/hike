(* The VSA: the pausable, in-place-growing solver and the def-origin
   stamp — the producer's public surface. *)
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

  (** The site materializer seam.  The callback owns target
      enumeration/validation and any lifting/solving; the solver installs
      the returned transfer in the source block and delivers its new case
      edges in the current fan-out. *)
  type materialize_transfer = Cbat_vsa.materialize_transfer

  (** A converged solve: the solution the worklist resolves from, the
      table its replay grew, and the persisted state a warm restart
      reuses. *)
  type solution = {
    sol : Cbat_vsa.vsa_sol;
    synth : Hike_synth.table;
    state : Cbat_vsa.run_state;
    sub : sub term;
  }

  type outcome = Solved of solution

  (** One solve pass under [callee], optionally on a persisted state.
      [resolved] is the extra-edge set, [seed] the warm solution, and
      [wake] the blocks whose phi set changed (an external restart). *)
  val solve :
    ?state:Cbat_vsa.run_state ->
    ?materialize_transfer:materialize_transfer ->
    Theory.Target.t ->
    lookup:lookup_fn ->
    images:section_image list ->
    callee:(Tid.t -> Cbat_vsa.Call_effects.callee) ->
    foreign_slots:Core.Int64.Set.t ->
    sub:sub term ->
    resolved:Tid.Set.t Tid.Map.t ->
    synth:Hike_synth.table ->
    seed:Cbat_vsa.vsa_sol option ->
    wake:Tid.Set.t ->
    outcome

  (** A warm seed: the old solution, with [woken] blocks' successors
      re-queued.  A woken entry re-reads the ABI seed. *)
  val warm_seed :
    abi:Hike_abi.t -> sub:sub term -> woken:Tid.Set.t -> ?old:sub term ->
    Cbat_vsa.vsa_sol -> Cbat_vsa.vsa_sol * Tid.Set.t

  (** The boundary stamp under the solve's image bracket. *)
  val stamp :
    images:section_image list -> synth:Hike_synth.table ->
    sol:Cbat_vsa.vsa_sol -> sub term ->
    (Cbat_vsa.AI.t * Cbat_vsa.AI.t) Tid.Map.t * sub term

  (** The construction-time round-down normalization, run on the initial
      body and on a batch's created blocks. *)
  val normalize_round :
    synth:Hike_synth.table ref -> sub term -> sub term

  (** The persistent registers a sub's defs write (partial defs at
      their base register). *)
  val written_regs_of_sub : synth:Hike_synth.table -> sub term -> Var.Set.t
