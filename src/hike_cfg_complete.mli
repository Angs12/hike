(* The CFG completion, fused into the solver's loop. *)
open Bap.Std

  (** The seam the solver passes in: [exp] denotes in [blk] (in the
      target def's before-env when [~def] is given). *)
  type denote =
    blk:blk term -> ?def:def term -> exp ->
    (Cbat_vsa.WordSet.t, Type.error) Result.t

  (** A dispatch site's case words with their guard subject: the
      target's own bounded denotation (no base, the target compared
      against each word), else the relative-offset table composed from
      the images (its base, and the base operands whose subtraction
      leaves the signed deltas the guards compare — the base
      materializes only to cancel against itself). *)
  val dispatch_words :
    denote:denote ->
    block_addrs:Tid.t Addr.Map.t ->
    last_defs:def term Var.Map.t ->
    sub:sub term ->
    blk:blk term ->
    ?images:Cbat_vsa.section_image list ->
    ?code_range:(int64 * int64) option ->
    exp -> (int64 option * exp list option * Cbat_word.t list) option

  (** The defs whose load address denotates, in the def's own
      before-env, to the stack-symbolic entry-RSP cell. *)
  val retaddr_defs :
    abi:Hike_abi.t -> sol:Cbat_vsa.vsa_sol -> sub term -> Tid.Set.t

  (** One resolution pass on the phase's solution: resolvable case
      words land on the run's map and resolved dispatches grow the
      extra edges.  Returns the sub, the edge set, the grown
      block-address map, the phase's dispatch facts (the site's
      address, its call class, the case words), and whether anything
      grew.  Runs under the caller's image bracket. *)
  val resolve_phase :
    abi:Hike_abi.t ->
    sol:Cbat_vsa.vsa_sol ->
    images:Cbat_vsa.section_image list ->
    block_addrs:Tid.t Addr.Map.t ->
    sub_addrs:Tid.t Addr.Map.t ->
    foreign_slots:Core.Int64.Set.t ->
    ?code_range:(int64 * int64) option ->
    sub term ->
    Tid.Set.t Tid.Map.t ->
    sub term * Tid.Set.t Tid.Map.t * Tid.t Addr.Map.t
    * (Addr.t * bool * Cbat_word.t list) list * bool

  (** The exit materialization at drain: the rewrites land once, then
      every block neither reachable from the sub's entry nor live
      behind a surviving indirect transfer drops ([foreign_slots] are
      the linker-owned slot addresses a transfer may read its target
      through — such a transfer leaves the program).  [images] is the
      table-coverage data. *)
  val materialize :
    abi:Hike_abi.t ->
    sol:Cbat_vsa.vsa_sol ->
    images:Cbat_vsa.section_image list ->
    block_addrs:Tid.t Addr.Map.t ->
    foreign_slots:Core.Int64.Set.t ->
    ?code_range:(int64 * int64) option ->
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
