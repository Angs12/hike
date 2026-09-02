(* Hike — the library's public interface.

   Everything a consumer needs crosses this seam. Consumers (test_cbat, the
   probe drivers, and any future tool) refer to these modules as
   [Hike.Abi], [Hike.Relevance], [Hike.Vsa], ... — never by the dune-internal
   [Hike__X] names, and never through the generated [Hike__.X] wrapper (whose
   resolution is unreliable).

   The aliases below are plain-name re-exports of this library's own modules.
   That form resolves identically under dune (wrapped: siblings see each other
   by plain name) and under bapbuild (flat: every module is a top-level module
   of the plugin), so ONE interface serves both builds.

   [Calling_conventions] is gone — the ABI facts live in the standalone
   [Abi] module (exported below), the sole origin of every register list
   and register predicate in the tree. Nor are the pass-pipeline internals
   in this file's implementation ([filter_subs], [compute_sub_sig],
   [convert_binary], ...) exported. [Hike_kb] IS exported, as [Kb] below —
   its join-domain slot is the supported way to hand per-sub VSA results
   across the pass chain. *)

open Bap.Std
open Bap_core_theory

(** Target-derived registers, sizes, and calling-convention facts.

    The SOLE origin for stack derivation and register identity — never
    hardcode a register name (AGENTS.md Principle 8). [Abi.sp] is the stack
    pointer; [Abi.of_target] yields the convention record. Its own library
    (hike.abi) sits at the bottom of the dependency lattice, shared by the
    vendored VSA libraries and this one. *)
module Abi = Hike_abi

(** Relevance Analysis — Stack Access tagging and the relevance closure.

    See [CONTEXT.md]; the contract is the [stack_access] / [relevant] /
    [dynamic_alloc] triple. *)
module Relevance : sig
  (** Tags a def whose RHS is a memory Load or Store whose address derives
      from the Stack Pointer. *)
  val stack_access : unit tag

  (** Tags the defs and phis that transitively contribute a value to a Stack
      Access address. *)
  val relevant : unit tag

  (** Tags a runtime-sized SP decrement (VLA / alloca). *)
  val dynamic_alloc : unit tag

  (** [analyze sp sub]: forward reachability from [sp] then a backward slice;
      tags [sub]'s defs with all three tags. *)
  val analyze : var -> sub term -> sub term

  (** [has_stack_access def]: is [def] tagged [stack_access]? *)
  val has_stack_access : def term -> bool

  (** [is_sp target var]: is [var] the target's stack pointer? *)
  val is_sp : Theory.Target.t -> var -> bool
end

(** The VSA: per-sub stack offset ranges (the [vsa_info] tag carrier).

    [offsets_of_sub] is the single producer of a sub's whole VSA result —
    including the STACK MODEL DECISION it carries in
    {!Convutils.vsa_info.stack_plan}. *)
module Vsa : sig
  (** [set_addr_bits n]: forward the target's address width into the VSA
      (the memmap's native key width). *)
  val set_addr_bits : int -> unit

  (** [offsets_of_sub target sp sub]: the per-def stack offset ranges,
      k-ranges, merged regions, the stack model decision, and the VLA
      bounds of [sub] — the [offsets]/[k_ranges] fields of the result
      are the precomputed per-def index maps (arch C2: no consumer folds
      them). Runs the relevance analysis first if [sub] carries
      no tags.

      [target] is threaded in so all stack derivation comes from
      {!Target}; [sp] is [Target.sp target]. *)
  val offsets_of_sub :
    Theory.Target.t -> var -> sub term -> Convutils.vsa_info
end

(** Dead-code elimination — the aggressive sweep lane.

    The interface is [dce] alone: the keep rule (the two-tier region-mem
    rule, the SP-erasure on the precise path, the always-keeps for ABI
    and memory traffic), the load-roots set, and the return-epilogue
    rewrite are the implementation, observable through [dce] on BIL
    fixtures. TOTAL over targets (a target without a convention record
    falls back to the x86_64 SysV facts). *)
module Dce : sig
  (** [dce ~target sub]: replace the lifted RETURN epilogue (the indirect
      noreturn call) with a var-free target, then iteratively sweep defs
      whose lhs nothing uses. Subs carrying the [Sub.intrinsic] attribute
      pass through unchanged. *)
  val dce :
    target:Theory.Target.t -> sub term -> sub term
end

(** Stack-to-locals — and the OWNER OF THE STACK MODEL DECISION.

    [split_plan] is the single producer of "does this sub's stack split
    into per-region [stack_rN] allocas, or fall back to one big
    [%frame]?" Its consumers are [stack_to_locals] itself, the DCE lane
    ({!Dce} — the SP-erasure keep) and [Bil2llvm] — no consumer
    re-derives it. *)
module Stack_to_locals : sig
  (** [stack_to_locals target sp sub]: rewrite constant-offset stack
      accesses to named locals, per the plan the vsa pass computed. *)
  val stack_to_locals : Theory.Target.t -> var -> sub term -> sub term

  (** [regions_of_sub sp target sub info ~frame_escaped]: merge [info]'s
      overlapping access ranges into Stack Regions (the connected
      components of the overlap graph), flagging each one's
      convertibility.

      [~frame_escaped] is the sub's {!frame_escapes} verdict, passed in
      (it is a per-region convertibility rule and it is computed once per
      sub by the producer). *)
  val regions_of_sub :
    var -> Theory.Target.t -> sub term -> Convutils.vsa_info ->
    frame_escaped:bool -> Convutils.region list

  (** [split_plan sp target sub info]: THE stack model decision — the
      convertible regions that become per-region [stack_rN] allocas, or
      [[]] for the sound single-frame fallback.

      Whole-sub rules, in order: a degraded VSA, an escaping frame
      address, an untagged / [Infinite] / [Unbounded] / [VLA] access, no
      convertible region, a VLA overlapping one, an uncovered tag, or an
      unsized region — each forces the fallback. *)
  val split_plan :
    var -> Theory.Target.t -> sub term -> Convutils.vsa_info ->
    Convutils.split_plan

  (** [sp_escaped sp target sub]: does an sp/fp-derived value ESCAPE the
      sub (reaching a call argument or a memory store's data)? — the
      value-escape half of the rule below. *)
  val sp_escaped : var -> Theory.Target.t -> sub term -> bool

  (** [frame_addr_alias sp target sub]: does a memory access read through a
      MATERIALIZED frame pointer (the [v := RSP; t := mem[v]] bare-copy
      class)? — the alias half of the rule below. *)
  val frame_addr_alias : var -> Theory.Target.t -> sub term -> bool

  (** [frame_escapes sp target sub]: is the sub's frame ADDRESSABLE FROM
      OUTSIDE, so its stack must stay in the one model frame?

      Finding 1: the UNIFIED rule — it replaces the two analyses that
      previously disagreed in both directions (stack-to-locals' value
      escape and the emitter's frame-pointer check). A sub whose frame is
      reachable from outside cannot split: a private [stack_rN] alloca
      would rebind the storage an outside pointer still points into. *)
  val frame_escapes : var -> Theory.Target.t -> sub term -> bool

  (** [region_bytes r]: the alloca size of region [r] (16-aligned, at least
      one byte) — the geometry the split model allocates. *)
  val region_bytes : Convutils.region -> int64

  (** [region_size_ok r]: the region's alloca size guard — one of the
      whole-sub rules of [split_plan] (an absurd span means the VSA did
      not converge, so the fallback frame covers it). *)
  val region_size_ok : Convutils.region -> bool

  (** [is_precise info]: does [info]'s sub use the split model? — the
      consumer-side read of the decision. *)
  val is_precise : Convutils.vsa_info -> bool

  (** The fission var producers + recognizers (mem-fission): the naming
      convention ([stack_rN_mem] / [stack_rN_base]) is THIS module's
      implementation detail. [region_mem id] / [region_base id] mint the
      vars; [is_region_mem] / [is_region_base] read them back. Consumers
      (the DCE lane's two-tier keep, the emitter's fission dispatch and
      its φ-lane name rule) import the predicates instead of re-typing
      the string grammar. *)
  val region_mem : int -> var
  val region_base : int -> var
  val is_region_mem : var -> bool
  val is_region_base : var -> bool
end

(** The per-sub VSA result store — one KB slot with a JOIN domain.

    [vsa_info] is a KB property on the hike run class whose domain is
    MAP EXTENSION (order) and MAP UNION (join): a provide that only adds
    subs the map lacks is a monotone update, a re-write of the same map
    is idempotent, and two DIFFERENT [vsa_info]s for the same sub raise
    [Toplevel.Conflict] — the KB's own conflict machinery, never a
    silent drop. Multiple subs (and multiple provides) accumulate;
    tests no longer need to borrow tids. *)
module Kb = Hike_kb

(** Shared pass/emitter vocabulary, re-exported wholesale: the [vsa_info] and
    [region] types above are defined here, and consumers build their literals
    (fixtures, region asserts) from these constructors. *)
module Convutils = Convutils

(** The LLVM emitter, re-exported for the geometry the tests pin
    ([region_bytes], [degraded_dims]).

    The emitter is a CONSUMER of the stack model decision — the decision
    itself is {!Stack_to_locals.split_plan}. *)
module Bil2llvm = Bil2llvm
