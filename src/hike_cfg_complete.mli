(* The CFG completion, fused into the solver's loop. *)
open Bap.Std

  (** The seam the solver passes in: [exp] denotes in [blk] (in the
      target def's before-env when [~def] is given). *)
  type denote =
    blk:blk term -> ?def:def term -> exp ->
    (Cbat_vsa.WordSet.t, Type.error) Result.t

  (** A dispatch site's case words with their guard subject: the
      denotation's bounded destination set, with the composed base
      operands whose subtraction leaves the signed deltas the guards
      compare (the base materializes only to cancel against itself, so
      the guards are PIE-safe).  A shape with no composed base compares
      the target against each word. *)
  val dispatch_words :
    denote:denote ->
    block_addrs:Tid.t Addr.Map.t ->
    last_defs:def term Var.Map.t ->
    sub:sub term ->
    blk:blk term ->
    exp -> (int64 option * exp list option * Cbat_word.t list) option

  (** The defs whose load address denotates, in the def's own
      before-env, to the stack-symbolic entry-RSP cell. *)
  val retaddr_defs :
    abi:Hike_abi.t -> sol:Cbat_vsa.vsa_sol -> sub term -> Tid.Set.t

  (** One resolution event pass on the phase's solution: the resolved
      dispatches contribute their target sets to the extra edges.  The
      words are the target denotations; the drive discovers the case
      bodies from the raw transfers' own denotations.  Returns the
      grown edge set and whether anything grew.  Runs under the
      caller's image bracket. *)
  val resolve_phase :
    abi:Hike_abi.t ->
    sol:Cbat_vsa.vsa_sol ->
    block_addrs:Tid.t Addr.Map.t ->
    foreign_slots:Core.Int64.Set.t ->
    sub term ->
    Tid.Set.t Tid.Map.t ->
    Tid.Set.t Tid.Map.t * bool

  (** The exit materialization at drain: the return canonicalization
      lands once, then every block neither reachable from the sub's
      entry nor live behind a surviving indirect transfer drops
      ([foreign_slots] are the linker-owned slot addresses a transfer
      may read its target through — such a transfer leaves the
      program).  The bounded dispatches materialize later, in
      [Split_blocks.materialize]. *)
  val materialize :
    abi:Hike_abi.t ->
    sol:Cbat_vsa.vsa_sol ->
    block_addrs:Tid.t Addr.Map.t ->
    foreign_slots:Core.Int64.Set.t ->
    sub term -> sub term

  (** The shape-only return canonicalization for a sub whose fixpoint
      did not converge (the pre-solution projection). *)
  val canonicalize_shape_returns : abi:Hike_abi.t -> sub term -> sub term

  (** Names every block's successors: a conditional goto's implicit
      false edge becomes an explicit [Goto], and a destination two jumps
      share collapses to one unconditional edge (ADR 0024). *)
  val materialize_fallthroughs : sub term -> sub term

  (** The noreturn fact's consumption: a call whose resolved target is a
      classified never-returning sub carries no return continuation, so
      the decode's fallthrough after it is not an edge. *)
  val clear_noreturn_returns : noreturn:Tid.Set.t -> sub term -> sub term

(** Rewrites a lifted term's direct targets: a call's target names a
    subroutine, a goto's a block, so the two resolve through different
    maps.  Indirect targets stay the resolution's own. *)
val remap_jmp :
  call:(Tid.t -> Tid.t) -> blk:(Tid.t -> Tid.t) -> jmp term -> jmp term

val guarded_cond : exp -> word list -> exp
val guard_of : jmp term -> exp option
val and_guard : exp option -> exp -> exp
