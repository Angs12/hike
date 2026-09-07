# 04 — Delete the never-hitting refinement memo

**Status:** ready-for-agent
**Depends on:** 03 (its producer totals are this ticket's baseline; do not confound
the two measurements)
**Blocks:** none

**What to build:** delete `Walk_memo` and its plumbing. The measurement behind this
ticket: 0 hits / 5280 lookups across the slow subs of both reference binaries, all
misses version-churn (`/tmp/opencode/cand4/measure.md` — inlined in the parent spec
against /tmp loss). A never-hitting cache is pure overhead (find + read-set
validity scan + add per visit) plus a soundness surface (stale-hit risk under the
exact churn measured); the miss path IS the definition, so removal executes the
identical path minus bookkeeping.

- [ ] Delete the `Walk_memo` instantiation, the find/add in the refinement entry,
      and the walk-read-set threading where it serves only the memo (keep the
      debug-only walk metrics — measurement still uses them).
- [ ] Delete the "walk reads subset the transfer reads" claim with the code that
      needed it. `Transfer_memo` (vertex path, unknown hit rate) stays untouched.
- [ ] No behavior change by construction: every visit runs the current miss path.

Gates:
- [ ] Corpus emission byte-identical to the 03-measured tree (re-emit and diff —
      any diff is a stop-and-report bug).
- [ ] Unit suite 0 FAIL (jne-counter, F1-FT, ticket-02 fixture green); structural
      asserts 0 failed; semantic gates at the known-failure floor.
- [ ] Producer totals neutral-or-better vs 03's numbers on the two reference
      binaries. Worse is a stop-and-report event (removing overhead must not cost).
- [ ] Report names every deleted site; the measurement delta (expected: small
      positive or zero) recorded with commands and tree hash.
