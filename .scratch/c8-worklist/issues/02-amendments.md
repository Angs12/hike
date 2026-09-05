# 02 — F1-B2 amendment + doc amendments

**Status:** blocked by 01
**Depends on:** 01 (the driver's behavior determines F1-B2's final letter)
**Blocks:** 03

**READ FIRST:** the C8 spec §2.6 + §4 (what changes about F1-B2 and the
docs); the current F1-B2 text in `test_cbat/test_properties.ml` (search
`F1-B2`); the C1 spec §2 (the trigger language being amended).

**Tasks:**

- [ ] F1-B2's letter amended: the comment + rationale change from
      per-SCC-allowance language to the behavioral core (both loops refine
      independently under the global budget — the starvation-regression
      pin). The assertions themselves should hold HUGELY (allowance is
      vast on fixtures) — if they DON'T, that is a finding, not a fixture
      bug: report it, do not weaken the pins.
- [ ] Confirm F1-B1/B3/B4 pass UNCHANGED (they never depended on the
      recharge site or the driver shape — if one fails, report which and
      how; it indicates scheduler-induced fixpoint shift, which is ticket
      03's verdict material).
- [ ] C1 spec §2 amended: the trigger (per-SCC `stabilize_scc`-entry →
      per-run fixpoint-start) with the one-paragraph reason (no
      stabilization episodes exist in a worklist); the enforcement half
      marked UNCHANGED.
- [ ] ADR-0002 addendum: one line (the visit scheduler changed; the deep
      walk's inline placement at every conditional jump is unchanged).

**Verification:** `dune runtest` green with the amended F1-B2 name in the
output.
