# 01 — Coreutils baseline (measurement only, no code)

**Status:** done (2026-09-02, tree @ d01ac20)
**Depends on:** the single-pass trace-partitioning spec COMPLETE ✅
**Blocks:** 02

**Deliverable:** /tmp/opencode/restriction-removal/baseline.md — the 103-binary
record: **59 PASS / 44 FAIL**, **llc class ZERO** (was 90 at worst), serial
lift 9600 s total (avg 18.6 s/binary), the 44-failure class breakdown (25
runtime crashes / 8 exit-code / 4 link / rest diffs), the corpus gate anchors
(32/32, 128/0, 30/2 knowns + 8/8, 484 tests), and the method notes (the OOM/
serial fix, the stale-BIR-cache trap, the plugin-race discipline, the restart
tolerance). The 44-failure work-list is ticket 04's differential reference.
