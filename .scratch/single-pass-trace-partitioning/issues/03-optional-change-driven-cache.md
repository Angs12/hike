# 03 — (optional, deferred) Change-driven cache to bound walk cost

**Status:** ready-for-agent
**Depends on:** 02
**Blocks:** none

**What to build:** the deep walk currently runs on every forward iteration (the
user explicitly accepted this cost in the grilling session — "accept the
complexity"). This ticket makes it cheap once the solution is stable: an edge's
backward walk is re-run only when its source block's OUT-state changed since the
last refine for that edge. Pure optimization — corpus emission is unchanged.

**Note:** NOT required by ADR 0002. Tracked only so the future bound is not lost.
Skip if the unconditional corpus + semantic gates are already within budget.

Acceptance criteria:
- [ ] Per-edge deep walk is cached; it re-runs only when the source block's
      OUT-state changed since the last refine for that edge.
- [ ] Corpus emission is byte-identical to 02 (no precision change).
- [ ] Measurable cost reduction on a representative binary (e.g. `stage_timer.exe`
      wall-time before/after).
- [ ] Gates green (see README): `dune runtest` all pass; `run_corpus.sh` 32/32
      rc=0; `check_allocas.sh` 128/0; semantics parity (29/3 + 8/8).

Gate: identical emission to 02, measurably faster fixpoint.
