(* The CFG completion, fused into the solver's loop. *)
open Bap.Std

  (** The seam the solver passes in: [exp] denotes in [blk] (in the
      target def's before-env when [~def] is given). *)
  type denote =
    blk:blk term -> ?def:def term -> exp ->
    (Cbat_vsa.WordSet.t, Type.error) Result.t

  (** A module-relative dispatch's base: the module-address var summand
      of the target's value read at a position the backward substitution
      reaches, with its link-time values.  The guards subtract the
      summand, so the base's relocation cancels and each case compares
      [word - base].  [site] is the position to bind the summand at when
      its var is rewritten before the transfer. *)
  type base = {
    summand : exp;
    values : int64 list;
    site : Hike_backsubst.form option;
  }

  (** A dispatch site's destination words (the target's bounded
      denotation) and its base, if module-relative.  [None] when no
      complete, sound case series exists. *)
  type dispatch = {
    words : Cbat_word.t list;
    base : base option;
  }

  (** A dispatch site's destination words: the target's bounded
      denotation.  [None] when it is not enumerable. *)
  val case_words :
    denote:denote ->
    block_addrs:Tid.t Addr.Map.t ->
    last_defs:def term Var.Map.t ->
    blk:blk term ->
    exp -> Cbat_word.t list option

  (** The words and the base, the base read by backward substitution
      over [graph], which must carry every dispatch's case edges. *)
  val dispatch_words :
    denote:denote ->
    graph:Hike_backsubst.graph ->
    block_addrs:Tid.t Addr.Map.t ->
    last_defs:def term Var.Map.t ->
    blk:blk term ->
    exp -> dispatch option

  type progress = Grew of Tid.Set.t Tid.Map.t | Drained of sub term

  (** Resolves the current solution, growing extra edges without changing
      the sub. Once no edges grow, canonicalizes returns, prunes proven
      unreachable blocks and names fallthroughs. Return-address and transfer
      classification belong to this call and cannot outlive its solution.
      Runs under the caller's image bracket. *)
  val advance :
    abi:Hike_abi.t -> sol:Cbat_vsa.vsa_sol -> synth:Hike_synth.table ->
    block_addrs:Tid.t Addr.Map.t -> foreign_slots:Core.Int64.Set.t ->
    sub term -> Tid.Set.t Tid.Map.t -> progress

  (** Names every block's successors: a conditional goto's implicit
      false edge becomes an explicit [Goto], and a destination two jumps
      share collapses to one unconditional edge (ADR 0024). *)
  val materialize_fallthroughs : sub term -> sub term

(** The destination word a dispatch arm tests, if [j] is one. *)
val arm_word : jmp term -> int64 option

(** The destination words not covered by the block's existing arms. *)
val remaining_words : blk term -> Cbat_word.t list -> Cbat_word.t list

(** Each indirect transfer gains, before it, one arm per destination word
    ([dests]) naming the start of one of the sub's blocks: a direct goto
    guarded by [target = word] over model addresses.  The transfer stays
    as the fallback for every word no arm tests. *)
val arm_dispatches : dests:(jmp term -> int64 list) -> sub term -> sub term

(** Rewrites a lifted term's direct targets: a call's target names a
    subroutine, a goto's a block, so the two resolve through different
    maps.  Indirect targets stay the resolution's own. *)
val guard_of : jmp term -> exp option
val and_guard : exp option -> exp -> exp
