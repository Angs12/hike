# T9 — the va_list re-model (P2, NEW 2026-09-10)

Spec: `.scratch/typed-model/spec.md` (binding constraints + the
conversion-first doctrine apply). Emerged from the T4 grilling: the
owner chose "re-model va_list" over a permanent window parameter; the
bridge ships in T4, this lane retires it.
Blocked-by: **T4** (the promotion + the SP Slot must land first — the
re-model consumes promoted parameters).
Blocks: nothing; after T9, NO sub takes a window parameter unless a
mixed unproven remainder demonstrably survives (measured, flagged).

## The measured class

va_arg_mixed (L1: the ud2 poison arm — re-attribute under the new
model first) and va_arg_vacopy (the va_list state round-trip: the
second va_copy'd pass reads a stale 6th element). The T4 bridge gives
variadic subs a caller_window parameter; this lane removes the need.

Design pre-digest: `.scratch/typed-model/t9-design-notes.md` (the
idiom map, the lift paths, the va_list storage facts, the two options'
transformation surfaces with soundness corners). READ IT FIRST. Its
asymmetry evidence DECIDES the design space:

**LAND option (a) — the alloca'd overflow array.** It is sound for the
DYNAMIC walk by LAYOUT (a dynamic GEP into the SysV-ordered array needs
no per-slot proof), serves the -O2 straight-line Caller reads and the
INLINED class (the -O2 vacopy walk lives inside `main`, which cannot be
declared LLVM-variadic — option (b) has NO rule for the exact residual
T9 targets, and its 1:1 walk-recognition is gate-shaped). Under (a) the
window parameter dies for the WHOLE variadic class. Respect the noted
soundness corners: the array-completeness size rule, the va_list
ESCAPE class (vprintf forwarding — absent from the corpus; flag, never
hack), and the check_allocas storage-shape assert.

**DE-SCOPED from this ticket:** va_arg_mixed — its failing -O2 lift
carries ZERO window traffic (no Caller/Mixed sites, no hike_stack
param); it is the L1 poison/alignment-guard class. If it flips during
T9's battery, attribute it to the L1 lane, not the re-model. The
va_arg_vacopy residual routes through the Caller lane + an untagged
raw-inttoptr over a reloaded-pointer phi (the state round-trip) —
re-attribute under T4's model FIRST, exactly as the doctrine says.

## Battery protocol (you hold the shared plugin slot in your wave)

Same as T1's (see `T1-opt-safety-regression.md` §Battery protocol):
`eval $(opam env)` first; `record_provenance.sh` after every install;
battery dirs on home disk.

Gates every iteration: `dune runtest` (the 8-failure owner baseline +
named surviving inventory; referee 0 mismatches), emission rc=0 both
lanes, strict -O0 semantics all PASS, check_allocas green, strict
opt-safety all PASS, the pinned -O2 gate — va_arg_mixed/va_arg_vacopy
flipping green is the EXPECTED outcome (proven flips update the golden
list + AGENTS.md in the same commit); a set GROWTH is a REGRESSION and
blocks.

## Acceptance

- All gates green; the variadic subs' signatures carry NO window
  parameter (grep the emissions).
- The convergence rows for the va_arg pair before/after in the
  verdict; the pin movement recorded deliberately.
- The re-model is one mechanism (the doctrine): grep the diff for
  window-threading residues and any new escape-shaped fact.

Worktree: `/home/tovpr/hike-t9`, branch `tm/t9-va-list`.
