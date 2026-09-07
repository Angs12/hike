# VH-06 — Extraction preserves variable floors (no const hulling)

**Status:** done (merged 51be2c9 2026-09-04; 612 ok / 0 FAIL; floors survive to plan)
**Depends on:** VH-00
**Blocks:** VH-01, VH-02

**What to build (fifth rule P1):** the extraction walk must not hull fired variable floors into const ranges — floors survive extraction as floors (the forced experiment measured nothing because 7 fired floors re-hulled to consts before the plan ran). Fixtures: extraction over a sub with floored defs yields floored tags (no hulling); const subs byte-identical behavior.

**Done when:** forced-floor reproduction (VH-00 procedure) shows floors surviving to the plan; suite green.
