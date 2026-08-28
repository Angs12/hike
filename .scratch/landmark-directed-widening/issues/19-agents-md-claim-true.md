# 19: Make AGENTS.md claim true (or correct it)

**What to build:** `AGENTS.md`'s claim ("Widening is LANDMARK-DIRECTED… landed 2026-08-23") reflects the code; if it cannot, correct the docs so implementation and documentation never diverge. Closes the loop on the recovery: docs match the durable golden state.

**Blocked by:** T18 (Coreutils 93/93 + semantic/allocas gates).

**Status:** ready-for-agent

- [ ] `AGENTS.md` §Widening matches the implemented landmark-directed widening (or is corrected with a recorded reason)
- [ ] No stale "threshold" claims remain that contradict the sole-extrapolation design
