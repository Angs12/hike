# VB-02 — Demand-driven ordering solver (standalone)

**Status:** done (merged cf7ece4 2026-09-04; 600 ok / 0 FAIL; solver uncalled)
**Depends on:** VB-01
**Blocks:** VB-04

**What to build:** the single home for bound comparison as a pure query function over domain state plus def order: canonicalize both sides to `(root, offset)` through the existing equality union-find (step zero) → live value sets (subset read) → construction order → unknown (caller collapses to Unbounded). Allocation sequencing falls out of the composed frame expression — no sequence field, no def walk. Fixture tests only (solver never called by production yet).

**Done when:** solver + fixtures green (same-root constant decisions, chain composition, per-layer pins with unknown-collapses), zero production diff.
