# 03 — Wall-time proof + report update

**Status:** ready-for-agent
**Depends on:** 01, 02
**Blocks:** none

**What to build:** the measured verdict plus the record.

- [ ] Producer totals and slowest-sub splits re-measured on the two large reference
      binaries (same probes, same subs as the relevance-free profile) against a
      same-day pre-change control; end-to-end lift wall times recorded alongside.
- [ ] Gate battery unchanged: unit suite (incl. jne-counter, F1-FT, new fixture)
      0 FAIL; corpus rc-clean; structural asserts 0 failed; semantic gates at the
      known-failure floor; probes crash-free.
- [ ] Verdict rule (fixed in advance): wall-time improvement with identical
      emission → bank it; neutral-or-worse with identical emission → revert the
      discipline change and keep the fixture (the prior spec's precedent).
      Precision movement in either direction is a stop-and-report event, not a
      verdict input — this change is precision-neutral by construction.
- [ ] Architecture-review HTML: update the refinement card with shape, oracle,
      numbers, and verdict; no new cards.
- [ ] Walk-extent work explicitly NOT attempted here.

Gates:
- [ ] Numbers recorded with commands and tree hashes; report updated in place.
