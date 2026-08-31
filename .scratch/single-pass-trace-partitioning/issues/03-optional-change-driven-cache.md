# 03 — (optional, deferred) Change-driven cache to bound walk cost

**Status:** wontfix (skipped-by-design, measured 2026-09-01 on `spec1-pr` @ edd71ac)
**Depends on:** 02 ✅
**Blocks:** none

**The measurement that closed it:** the full 32-binary corpus emission
(`run_corpus.sh`, including lifting + all 32 per-sub fixpoints with the inline
deep-walk refinement + emission) runs in **~18 s wall / 14.6 s user** on the
merged branch — the same envelope as the pre-fusion baseline (ticket-01's
report: "the full corpus emits in the same wall-time envelope as baseline";
`factorial`'s corpus_watch fixpoint time ~0.0 s). The ADR-0002 cost fear
(O(edges × iterations) nested walks) does not materialize at corpus scale:
the fixpoint's own solution convergence dominates, and once stable each
re-refine is a cheap re-run.

The ticket's own note said: "Skip if the unconditional corpus + semantic gates
are already within budget." They are. Reopen ONLY if the coreutils-scale
differential (spec 2's §5, `.scratch/restriction-removal/spec.md`) shows a
per-sub wall blowup that the cheapening lane (its Proposal C) can't cover —
the cache design is recorded below for that contingency.

**The contingency design (for whoever reopens):** key per (source block,
out-edge) on the source block's OUT-state identity — re-run the walk only
when `AI.equal` fails against the cached OUT (the `AI.equal old incoming`
stability check at the widening head is the model to copy; report-02 notes
the snapshot is already O(1) per vertex visit). Byte-identity to 02's
emission is the acceptance gate.

Original acceptance criteria (kept for the record):
- [ ] Per-edge deep walk cached; re-runs only on OUT-state change.
- [ ] Corpus emission byte-identical to 02.
- [ ] Measurable cost reduction on a representative binary.
