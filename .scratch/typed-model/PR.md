# The typed-model program — convergence, soundness, simplicity

Implements the spec at `.scratch/typed-model/spec.md` (label:
ready-for-agent, settled 2026-09-10). One ordered program on one
branch:

| ticket | what | size |
|---|---|---|
| [T1](/.scratch/typed-model/tickets/T1-opt-safety-regression.md) | the typed-model opt-safety regression (nested_struct, struct_by_value) — the general address-materialization rule | M |
| [T2](/.scratch/typed-model/tickets/T2-simplification-pass.md) | the simplification pass (orphans of the removals) | S |
| [T3](/.scratch/typed-model/tickets/T3-symbolic-stack-base.md) | the symbolic stack base + single-channel tagging (absorbs T7) | M |
| [T4](/.scratch/typed-model/tickets/T4-stack-arg-promotion.md) | stack-arg promotion (the convergence class) | M |
| [T5](/.scratch/typed-model/tickets/T5-sse-lane-def-use.md) | L3: the SSE lane def-use fidelity | M |
| [T6](/.scratch/typed-model/tickets/T6-data-relocation-rendering.md) | L4: data-section relocation rendering (fptr_table) | M |

T7 is dissolved into T3 (the uniform materialization rule leaves no
sign cases). T8 (the 8 pre-existing unit failures) is ready-for-human —
out of this program's scope.

Dependency order: T1 → T3 → T4 → T5, with T2 and T6 independent
(merged as their branches complete). Every ticket lands behind the
full battery (`dune runtest` + referee, corpus emission, strict -O0
semantics, check_allocas, strict opt-safety, the pinned -O2 gate, the
convergence report), each verdict reporting its red-list and
convergence movement. The pin moves only in commits that deliberately
change it.

Closes the spec issue `.scratch/typed-model/spec.md` and tickets
T1–T6.
