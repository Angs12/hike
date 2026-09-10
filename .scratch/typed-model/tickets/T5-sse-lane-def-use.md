# T5 — L3: the SSE lane def-use fidelity (P2)

Spec: `.scratch/typed-model/spec.md` (binding constraints + the
conversion-first doctrine apply). Re-scoped 2026-09-10 late to the
4-knowns world.
Blocked-by: **T4** (its promotions change the measured class; the
convergence accounting order holds).
Blocks: nothing.

## The measured class (post-T3c)

The -O2 pin holds at 4: byte_copy, union_overlap (the L3 class),
va_arg_mixed (L1), va_arg_vacopy (the va_list round-trip — T9's).
fizzbuzz_safe and fptr_table flipped green in T3c and are OUT of this
ticket. array_local's ~0.18 convergence gap and the four T4
indirect-call corpus sources' -O2 shapes join the measured scope.

## What lands

Lane-consuming ops must meet the lane defs written EARLIER IN THE SAME
ITERATION (the producer-subtraction discipline over memory words), and
vector store loops must advance. The words lane is already the sole
provenance carrier (T3/T3c); this ticket makes its def-use faithful
enough that the SSE classes lift to correct, folded results.

## Battery protocol (you hold the shared plugin slot in your wave)

Same as T1's (see `T1-opt-safety-regression.md` §Battery protocol):
`eval $(opam env)` first; `record_provenance.sh` after every install;
battery dirs on home disk.

Gates every iteration: `dune runtest` (failure set == the 8-failure
owner baseline + T4's surviving inventory, each named; referee 0
mismatches), emission rc=0 both lanes, strict -O0 semantics all PASS,
check_allocas green, strict opt-safety all PASS, the pinned -O2 gate —
the failing set may only change by a PROVEN flip (byte_copy /
union_overlap are the expected candidates; each flip updates the
golden list + AGENTS.md in the same commit, with the mechanism named).

## Acceptance

- All gates green per above; pin movement only as proven flips.
- **Convergence movement**: the convergence-report rows for
  byte_copy, union_overlap, array_local (+ the new indirect sources)
  before/after in the verdict file.
- The def-use rule is the producer-subtraction discipline (no
  iteration-boundary gates, no "wait for next iteration" stops).

Worktree: `/home/tovpr/hike-t5`, branch `tm/t5-sse-lane`.
