open Bap_core_theory
open Bap.Std

(** [dce ~target ~escape_roots sub] sweeps dead defs and phis: the
    roots are every jump's reads — its operand expressions plus the
    kind's ABI boundary reads (a return edge reads the return registers
    and SP; a call the parameter registers, the ABI return registers it
    produces, and SP), a call-bearing block's mem-typed defs, and the
    sub's escape roots (the storages whose bytes leave the sub) — and a
    def or phi is live iff its lhs is read by a live node, to a
    fixpoint.  Liveness is per storage: the reads and the lhs project to
    base vars, so a load of any SSA version of a mem var roots the
    stores into it. *)
val dce :
  target:Theory.Target.t ->
  escape_roots:Var.Set.t ->
  Bap.Std.sub Bap.Std.term ->
  Bap.Std.sub Bap.Std.term
