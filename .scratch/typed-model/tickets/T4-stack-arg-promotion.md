# T4 — stack-arg promotion (P1)

Spec: `.scratch/typed-model/spec.md` (binding constraints apply).
Design: `.scratch/o2-attribution/tickets/05-stack-arg-promotion.md`
(the settled ticket: measured baseline, mechanism insight, risks).
Blocked-by: **T3** (the tag/key universe it matches against).
Blocks: T5 (the convergence accounting order).

## What lands

ALL stack args pass as call arguments — uniformly, no provenness
condition, no per-slot cases (the SysV convention fixes the
correspondence: the callee's incoming slots at `[entry_rsp + 8 + 8·i]`;
each caller stores the same slot relative to the call's rsp):

- the CALLEE's incoming stack-cell loads (positive-offset, bounded
  ranges) become reads of new function parameters (one per distinct
  slot, width per the loaded width);
- the CALLER's corresponding outgoing stores become direct call
  arguments at the call site;
- slots that are unproven (Unbounded/dynamic/indirect calls) stay on
  the memory path — that is the complete-rule fallback, not a gate.

The `hike_stack`/rebase path is untouched for non-slot accesses.
Signature churn re-baselines the affected IR (deliberate).

## Battery protocol (you hold the shared plugin slot in your wave)

Same as T1's (see `T1-opt-safety-regression.md` §Battery protocol):
you are the wave's only `bap`/`dune install` user;
`record_provenance.sh` after every install; battery dirs on home disk.

Gates every iteration: `dune runtest`, -O0 emission 33/33 rc=0, strict
-O0 semantics **33/33** (the primary oracle must not move),
check_allocas green, strict opt-safety 33/33, -O2 emission rc=0,
pinned -O2 gate: the failing set may only change by a PROVEN flip
(then the golden list + AGENTS.md move in the same commit — never a
rider).

## Acceptance

- All gates green per above.
- **Convergence movement** (the ticket's prize — measure with
  `scripts/semantic/convergence_report.sh <c0> <c2> <lift0> <lift2>
  <workdir>`): the memory-passed class collapses toward its o2+opt
  counts — deep_chain 323/4, spill_many 134/4, many_args 133/4,
  alloca_vla 95/4, nested_calls 75/4, union_overlap 166/4,
  mixed_fp_int 68/4. Every row before/after goes in the verdict file.
- The promotion is total over proven pairs; grep the diff for
  provenness conditions (they are banned).

Worktree: `/home/tovpr/hike-t4`, branch `tm/t4-stack-args`.
