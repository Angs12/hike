# VH-01 — Bounded single-spill equality rule

**Status:** done (merged a338f45 2026-09-04; 654 ok / 0 FAIL; verdict 0/8 — target unreachable by mechanism, re-grill pending)

**Note (VH-00 fifth rule P0):** the escape veto stays independently binding — VH-03 remains necessary regardless.

**What to build:** the mirror keeps a spilled variable's equality through one stack cell and one load/store pair while the cell's base is untouched; a store to an unknown offset folds the cell and kills the equality. No general memory reasoning. Fixtures: spill keeps equality; unknown-offset store kills it; two-cell chains stay havoc; V29 precedent stays green.

**Done when:** verdict moves measurably on the dissecting binary (target 7/8 dynamic defs firing, counted via dump_tags); suite green; per-lock payoff recorded.
