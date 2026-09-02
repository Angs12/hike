(* Hike_dce — the aggressive DCE lane of the hike pipeline.

    The interface is [dce] alone. The keep rule (the two-tier region-mem
    rule, the SP-erasure on the precise path, the always-keeps for ABI
    and memory traffic), the load-roots set, and the return-epilogue
    rewrite are the implementation — all observable through [dce] on BIL
    fixtures (see the Dce tests in test_cbat).

    [dce] is TOTAL over targets: a target without a convention record
    (the unit fixtures' [Theory.Target.unknown]) falls back to the
    x86_64 SysV record's register facts; the SP-erasure lane skips
    (no stack pointer), which is the sound identity for a fixture
    without SP-relative traffic. *)

open Bap_core_theory

(** [dce ~target sub]: replace the lifted RETURN epilogue (the indirect
    noreturn call) with a var-free target, then iteratively sweep defs
    whose lhs nothing uses — memory writes, ABI register defs and
    [intrinsic:*] interface vars always survive, EXCEPT the fissioned
    region mem vars ([stack_rN_mem]), which survive iff some Load reads
    them (the load-roots rule). Subs carrying the [Sub.intrinsic]
    attribute pass through unchanged. *)
val dce : target:Theory.Target.t -> Bap.Std.sub Bap.Std.term ->
  Bap.Std.sub Bap.Std.term
