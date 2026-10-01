(* The CFG completion, fused into the solver's loop. *)
open Bap.Std

  (** The seam the solver passes in: [exp] denotes in [blk] (in the
      target def's before-env when [~def] is given). *)
  type denote =
    blk:blk term -> ?def:def term -> exp ->
    (Cbat_vsa.WordSet.t, Type.error) Result.t

  (** The defs whose load address denotates, in the def's own
      before-env, to the stack-symbolic entry-RSP cell. *)
  val retaddr_defs :
    abi:Hike_abi.t -> sol:Cbat_vsa.vsa_sol -> sub term -> Tid.Set.t

  (** One resolution pass on the phase's solution: resolvable case
      words land on the run's map (mid-block entries split their
      block, additively) and resolved dispatches grow the extra
      edges.  Returns the sub, the edge set, the fresh entry blocks,
      the grown block-address map, and whether anything grew.  Runs
      under the caller's image bracket. *)
  val resolve_phase :
    abi:Hike_abi.t ->
    sol:Cbat_vsa.vsa_sol ->
    lift_at:(Addr.t -> block_addrs:Tid.t Addr.Map.t -> blk term list option) ->
    block_addrs:Tid.t Addr.Map.t ->
    sub_addrs:Tid.t Addr.Map.t ->
    sub term ->
    Tid.Set.t Tid.Map.t ->
    sub term * Tid.Set.t Tid.Map.t * Tid.Set.t * Tid.t Addr.Map.t * bool

  (** The exit materialization at drain: canonical returns,
      complete-only guarded-goto series, and the prune retracts split
      structure the materialization didn't claim.  [images] is the
      table-coverage data. *)
  val materialize :
    abi:Hike_abi.t ->
    sol:Cbat_vsa.vsa_sol ->
    images:Cbat_vsa.section_image list ->
    block_addrs:Tid.t Addr.Map.t ->
    fresh:Tid.Set.t ->
    sub term -> sub term

  (** The shape-only return canonicalization for a sub whose fixpoint
      did not converge (the pre-solution projection). *)
  val canonicalize_shape_returns : abi:Hike_abi.t -> sub term -> sub term

  (** Names every block's successors: a conditional goto's implicit
      false edge becomes an explicit [Goto], and a destination two jumps
      share collapses to one unconditional edge (ADR 0024). *)
  val materialize_fallthroughs : sub term -> sub term

(** Rewrites a lifted term's direct targets: a call's target names a
    subroutine, a goto's a block, so the two resolve through different
    maps.  Indirect targets stay the resolution's own. *)
val remap_jmp :
  call:(Tid.t -> Tid.t) -> blk:(Tid.t -> Tid.t) -> jmp term -> jmp term
