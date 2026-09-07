# VH-04 — Flagship isolation proof on alloca_vla

**Status:** needs-triage
**Depends on:** VH-01, VH-02, VH-03
**Blocks:** VH-05

**What to build:** no new mechanism expected — measure: with floors firing (VH-01), sizes bounded (VH-02), and spill traffic unvetoed (VH-03), does `buf`-above-both isolate into a converting region by allocation sequence? If yes, pin it (region assertion + stdout identity). If a fifth rule surfaces, it becomes a ticket and this ticket re-scopes to it.

**Done when:** `alloca_vla` converts ≥1 disjoint region with byte-identical stdout, pinned; or the fifth rule is ticketed with experiment output.
