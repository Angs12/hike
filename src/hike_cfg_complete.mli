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

  (** Names every block's successors: a conditional goto's implicit
      false edge becomes an explicit [Goto], and a destination two jumps
      share collapses to one unconditional edge (ADR 0024). *)
  val materialize_fallthroughs : sub term -> sub term

(** The destination word a dispatch arm tests, if [j] is one. *)
val arm_word : jmp term -> int64 option

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
