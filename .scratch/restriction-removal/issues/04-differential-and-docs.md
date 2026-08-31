# 04 — Coreutils differential + validation record + AGENTS.md refresh

**Status:** ready-for-agent
**Depends on:** 03 (the full change landed; 01's baseline recorded)
**Blocks:** none

**What to build:** the spec's §5.2 differential and §6's validation record —
the first measured cost statement of the unrestricted VSA, plus the standing
documentation rewrite.

- [ ] The coreutils pipeline re-run (same script, same out-root, distinct
      dir `/tmp/opencode/restriction-removal/post-coreutils`); per-sub wall
      deltas computed against ticket 01's `baseline.md` and recorded in
      `/tmp/opencode/restriction-removal/differential.md`.
- [ ] Budget-trigger evaluation (§5.2): any sub > 10 s wall (or > 2× its
      baseline) → the denotation-cheapening lane (proposal C, §5.3's
      pre-registered scope) is OPENED as a follow-up ticket with the
      measured profile naming the stage. NEVER a gate; a cost record.
- [ ] Semantic comparison vs the baseline's PASS/FAIL summary — no
      regressions; any flips (either direction) recorded per binary.
- [ ] AGENTS.md §CURRENT VALIDATION STATE rewritten with fresh numbers +
      fresh timestamp (per the standing NON-NEGOTIABLE directive), including
      the precision-probe table and the differential summary.
- [ ] The spec's Status header updated: implementation COMPLETE with the
      commit hash; any §2.4 prediction that did NOT materialize recorded
      next to it (the spec asked for verification, not confirmation).

Gate: the two measurement files + the refreshed AGENTS.md committed.
