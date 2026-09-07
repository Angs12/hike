# VB-01 — Generalize Range bounds to `const | var + k` (dark)

**Status:** done (merged 7d42046 2026-09-04; 585 ok / 0 FAIL; dark by construction)
**Depends on:** none
**Blocks:** VB-02, VB-03

**What to build:** the bound syntax in the domain vocabulary gains the variable arm (`const | var + k` per side, independently); joins with var mismatch collapse the side to Unbounded (the sound identity); widening translates constant offsets only, preserves var identity, collapses on var redefinition. Fixture tests only: no producer emits a variable floor, so the suite is green trivially and behavior is byte-identical.

**Done when:** new syntax + fixtures green, zero production-behavior diff, zero behavior change on all gates.
