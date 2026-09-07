# 03 — Wall-time proof + report fold-in

**Status:** ready-for-agent
**Depends on:** 01, 02
**Blocks:** none

**What to build:** the measured verdict on the merged candidate, plus the record.

- [ ] Producer totals and slowest-sub splits re-measured on the two large reference
      binaries (same probes, same subs as the relevance-free profile); end-to-end
      lift wall time recorded alongside.
- [ ] Gate battery unchanged: unit suite 0 FAIL, corpus emission rc-clean,
      structural asserts 0 failed, semantic gates at the known-failure floor, probes
      crash-free.
- [ ] Architecture-review HTML: fold the merged candidate into the transfer-tax
      card (memo shape, oracle, version discipline, measured numbers); mark the
      absorbed candidate closed-by-merge. No new cards.
- [ ] Seed-only extent reduction explicitly NOT attempted here; if measurement
      shows the memo under-delivering, open it as a follow-up gated on the oracle
      plus probe deltas (never inline it into this ticket).

Gates:
- [ ] Numbers recorded with commands and tree hash; report updated in place.
