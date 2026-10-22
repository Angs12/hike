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
    ?cap:int ->
    denote:denote ->
    block_addrs:Tid.t Addr.Map.t ->
    last_defs:def term Var.Map.t ->
    blk:blk term ->
    exp -> Cbat_word.t list option

  (** The indirect transfer's target expression, unless it is a
      return-address read or a linker-owned slot read (neither is a
      dispatch).  [last_defs] is the block's own last-def map. *)
  val dispatch_target :
    synth:Hike_synth.table -> last_defs:def term Var.Map.t ->
    retaddr:Tid.Set.t -> index:Hike_transfer.index ->
    foreign_slots:Core.Int64.Set.t -> jmp term -> exp option

  (** The words and the base, the base read by backward substitution
      over [graph], which must carry every dispatch's case edges. *)
  val dispatch_words :
    ?cap:int ->
    denote:denote ->
    graph:Hike_backsubst.graph ->
    block_addrs:Tid.t Addr.Map.t ->
    last_defs:def term Var.Map.t ->
    blk:blk term ->
    exp -> dispatch option

  (** A site materialization's intra-sub case target: validated address,
      final tid, lifted fragment. *)
  type case = int64 * Tid.t * sub term

  (** An exact block edge: source block, destination block. *)
  type edge = Tid.t * Tid.t

  (** One staged builder run's result.  [delta_sub] is the complete
      rewritten sub (source, new blocks, old targets) after SSA and DCE;
      [new_edges] are the exact source/new-block edges. *)
  type delta = {
    delta_sub : sub term;
    delta_synth : Hike_synth.table;
    new_blocks : Tid.Set.t;
    new_edges : edge list;
    woken : Tid.Set.t;
  }

  (** Materialize a site: [working] already carries the rewritten source
      and trap; Prepare inserts the missing decoded case blocks, Create
      normalizes them, Wire records the exact source/new-block edges, and
      Finalize runs [Hike_ssa.update_sub_woken] over the complete rewrite
      against the pre-rewrite [old] sub, then DCEs the created blocks.
      [cases] are the validated target address, its final tid, and its
      lifted fragment. *)
  (** Retire a retained jump fallback when the no-match condition over
      its arms proves the target bottom.  No targets are materialized. *)
  val retire_jump_fallbacks :
    sol:Cbat_vsa.vsa_sol -> synth:Hike_synth.table -> sub term -> sub term

  val materialize_site :
    target:Bap_core_theory.Theory.Target.t ->
    abi:Hike_abi.t ->
    callee_tid:(Tid.t -> Tid.t) ->
    rip_address:(int64 -> bool) ->
    claim:(sub term -> sub term) ->
    synth:Hike_synth.table ->
    block_addrs:Tid.t Addr.Map.t ->
    old:sub term ->
    working:sub term ->
    cases:case list ->
    edges:edge list ->
    delta

  (** Each block's term-order follower: the false edge of a conditional
      goto whose block has no explicit one. *)
  val term_follower : sub term -> Tid.t -> Tid.t option

  (** The exit materialization at drain: the return canonicalization
      lands once, then every block neither reachable from the sub's
      entry nor live behind a surviving indirect transfer drops
      ([foreign_slots] are the linker-owned slot addresses a transfer
      may read its target through — such a transfer leaves the
      program).  Fallthroughs are completed before the solve; a source
      rewritten by a site install is not a term-order conditional jmp.
      [retaddr] is the sub's [retaddr_defs]; the sub and call facts
      must be unchanged since. *)
  val materialize :
    sol:Cbat_vsa.vsa_sol ->
    synth:Hike_synth.table ->
    block_addrs:Tid.t Addr.Map.t ->
    foreign_slots:Core.Int64.Set.t ->
    retaddr:Tid.Set.t ->
    sub term -> sub term

  (** The return-address definitions of [sub] under [sol]. *)
  val retaddr_defs :
    abi:Hike_abi.t ->
    synth:Hike_synth.table ->
    sol:Cbat_vsa.vsa_sol ->
    sub term -> Tid.Set.t

  (** Names every block's successors: a conditional goto's implicit
      false edge becomes an explicit [Goto], and a destination two jumps
      share collapses to one unconditional edge (ADR 0024). *)
  val materialize_fallthroughs : sub term -> sub term

(** Rewrites a lifted term's direct targets: a call's target names a
    subroutine, a goto's a block, so the two resolve through different
    maps.  Indirect targets stay the resolution's own. *)
val guard_of : jmp term -> exp option
val and_guard : exp option -> exp -> exp
