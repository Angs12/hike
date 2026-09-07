# VH-03 — Shared spill predicate at the escape rule

**Status:** needs-triage
**Depends on:** VH-01
**Blocks:** VH-04

**What to build:** the escape rule learns VH-01's distinction through one shared predicate: a spill to a dead cell is not an escape. Verdict traffic must not be vetoed by the sibling rule. Fixtures: spill-to-dead-cell escapes nothing; genuine escapes (arg-register derived values, non-spill stores) still veto.

**Done when:** the merged plan on the dissecting binary is no longer vetoed on spill traffic alone; suite green; payoff counted.
