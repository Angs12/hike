# 01 — Referee & Synthetic Fixtures for Directional Infs

**Status:** ready-for-agent  
**Depends on:** (none — the frontier ticket)  
**Blocks:** 02, 03, 04, 05  

**READ FIRST:**
- The spec: `.scratch/directional-infs/spec.md` (specifically §1, §2, §4, §5)
- The research note: `.scratch/directional-infs/research.md` (specifically §1.2, §4, §5)
- Referee harness: `zz_scratch_probe/clpequiv.ml`

**Tasks:**
- [ ] In `zz_scratch_probe/clpequiv.ml`, add unit/property test helpers for directional sets:
  - Checking stable-bound widening behavior: `widen_join {8} {8, 16}` must retain lower bound 8.
  - Checking ray properties: `min_elem` on an ascending ray with base 8 returns `Some 8`.
  - Checking meet truncation: intersecting an ascending ray `[8, +inf)` with finite range `[0, 64]` returns finite `[8, 64]`.
- [ ] Add a synthetic unit fixture in `test_cbat/` or `test_cbat/test_cbat.ml` asserting the target property on a synthetic BIR loop that increments a cell starting at 8.
- [ ] `dune runtest` passes with baseline suites green.

**Verification:**
- `dune exec zz_scratch_probe/clpequiv.exe` builds and runs cleanly.
