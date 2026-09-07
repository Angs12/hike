# 01 — Fused bounds+equalities domain, standalone

**Status:** done (merged b2ecfea 2026-09-03; 523 ok / 0 FAIL)
**Depends on:** none
**Blocks:** 02

**What to build:** the new fused-domain file in the domain library: per-var bounds (bounds-only interval half, strides explicitly not carried) plus affine-equality relations over the shared expression syntax with the frame relation. Join (affine hull + bound meet), meet, equal, transfer stubs, joins-only reduction, split-widening hooks (bounds widen as today, equalities pass through). Fixture tests only: no production module imports it, so the suite is green trivially.

**Must include:** stride-sensitive fixtures that name the conceded precision (F1-NEQ-shaped counter behavior marked as expected-difference vs intervals); bound-pair merge-verdict fixtures needing no fixpoint; equality derivation fixtures (`x=y+k` through copies/spills).

**Done when:** new file + fixtures green, zero production diff, zero behavior change.
