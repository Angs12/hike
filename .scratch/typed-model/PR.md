# The typed-model program — convergence, soundness, simplicity

Implements the spec at `.scratch/typed-model/spec.md` (label:
ready-for-agent, settled 2026-09-10; updated late 2026-09-10 with the
doctrine's final form). One ordered program on one branch
(`typed-model-program`).

| ticket | what | size | state |
|---|---|---|---|
| [T1](/.scratch/typed-model/tickets/T1-opt-safety-regression.md) | the typed-model opt-safety regression (nested_struct, struct_by_value) — the general address-materialization rule | M | **landed** (merge `5b94a46`) |
| [T2](/.scratch/typed-model/tickets/T2-simplification-pass.md) | the simplification pass (orphans of the removals) | S | **landed** (merge `8d600ac`) |
| [T3](/.scratch/typed-model/tickets/T3-symbolic-stack-base.md) | the symbolic stack base + single-channel tagging (absorbs T7) | M | **landed** (merge `d2b66d7`) |
| [T6](/.scratch/typed-model/tickets/T6-data-relocation-rendering.md) | L4: data-section relocation rendering (fptr_table) | M | **landed** (merged in wave 1) |
| [T3c](/.scratch/typed-model/tickets/T3c-single-predicate.md) | the escape dies entirely — the denotation is the one mechanism; the -O2 pin 6 → 4 | M | **landed** (merge `7a41070`) |
| [T4](/.scratch/typed-model/tickets/T4-stack-arg-promotion.md) | stack-arg promotion + the SP convention + VSA-resolved indirect calls + internal thunks | L | **frontier** (worktree `/home/tovpr/hike-t4`, branch `tm/t4-stack-args`) |
| [T5](/.scratch/typed-model/tickets/T5-sse-lane-def-use.md) | L3: the SSE lane def-use fidelity (byte_copy, union_overlap, array_local + the T4 sources) | M | blocked-by T4 |
| [T9](/.scratch/typed-model/tickets/T9-va-list-remodel.md) | the va_list re-model — retire the caller-window parameter for variadic subs | M | blocked-by T4 |

T7 is dissolved into T3/T3c/T9 (the L2 mechanism is structurally
deleted; the va_arg_vacopy residual is the va_list state round-trip —
T9 owns it; va_arg_mixed stays L1 pending re-attribution under the new
model). T8 (the 8 pre-existing unit failures) is ready-for-human — out
of this program's scope.

Dependency order: T1 → T3 → T3c → T4 → {T5, T9} (T5/T9 both consume
T4's promotions; the plugin-slot waves are serialized — each ticket's
battery protocol holds the shared slot for its wave). Every ticket
lands behind the full battery (`dune runtest` + referee, corpus
emission both lanes, strict -O0 semantics, check_allocas, strict
opt-safety, the pinned -O2 gate, the convergence report), each verdict
reporting its red-list and convergence movement. The pin
(`o2_known_failures.txt`) moves only in commits that deliberately
change it — currently the four (byte_copy, union_overlap, va_arg_mixed,
va_arg_vacopy) at 29/4.

Closes the spec issue `.scratch/typed-model/spec.md` and tickets
T1–T6, T3c, T5, T9.
