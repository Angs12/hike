# T5 — L3: the SSE lane def-use fidelity (P2)

Spec: `.scratch/typed-model/spec.md` (binding constraints apply).
Mechanism record: `.scratch/o2-attribution/verdict.md` §L3 (the
runtime-proven lane-promotion def-use failures).
Blocked-by: **T4** (its convergence accounting supersedes the stale
numbers; the words lane is the sole provenance carrier after T3).
Blocks: nothing.

## What lands

Lane-consuming ops must meet the lane defs written EARLIER IN THE SAME
ITERATION (the producer-subtraction discipline over memory words), and
vector store loops must advance. The measured class: byte_copy,
union_overlap, fizzbuzz_safe's residual (lifted-ud2 reachable via the
L3-wrong lane values), array_local's partial. array_local's ~0.18
convergence gap is the quantified target.

This is the words/memory lane of the VSA (cell meets, the loop-advance
of vector stores) — the stack-base-symbolic record notes these def-use
fixes are what make the words lane trustworthy as the sole provenance
carrier; after T3 they stand alone here.

## Battery protocol (you hold the shared plugin slot in your wave)

Same as T1's (see `T1-opt-safety-regression.md` §Battery protocol):
you are the wave's only `bap`/`dune install` user;
`record_provenance.sh` after every install; battery dirs on home disk.

Gates every iteration: `dune runtest`, -O0 emission 33/33 rc=0, strict
-O0 semantics **33/33**, check_allocas green, strict opt-safety 33/33,
-O2 emission rc=0, pinned -O2 gate: the failing set may only change by
a PROVEN flip (byte_copy/union_overlap/fizzbuzz_safe are the expected
candidates — each flip updates the golden list + AGENTS.md in the same
commit, with the mechanism named).

## Acceptance

- All gates green per above; pin movement only as proven flips.
- **Convergence movement**: the convergence report rows for
  byte_copy, union_overlap, fizzbuzz_safe, array_local before/after
  in the verdict file (the biggest convergence lever after T4).
- The def-use rule is the producer-subtraction discipline (no
  iteration-boundary gates, no "wait for next iteration" stops).

Worktree: `/home/tovpr/hike-t5`, branch `tm/t5-sse-lane`.
