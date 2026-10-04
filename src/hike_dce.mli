open Bap_core_theory

(** [dce ~target sub] sweeps dead defs and phis: the roots are every
    jump's reads — its operand expressions plus the kind's ABI boundary
    reads (a ret consumes the return registers and SP, a call the
    parameter registers and SP) — and a def or phi is live iff its lhs
    is read by a live node, to a fixpoint. *)
val dce : target:Theory.Target.t -> Bap.Std.sub Bap.Std.term ->
  Bap.Std.sub Bap.Std.term
