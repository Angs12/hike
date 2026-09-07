# VB-04 — Split-plan retarget to variable floors

**Status:** done (merged 5918674 2026-09-04; 605 ok / 0 FAIL; alloca_vla acceptance structurally unmet — zero floors corpus-wide, part-documented)
**Depends on:** VB-02, VB-03
**Blocks:** VB-05

**What to build:** the split plan reads variable floors directly for overlap (spans stay int64 display-only; no conversion decision reads a span where a floor exists); region merging by may-subset (survivor keeps lower low, high side collapses unless subset-proven); dynamic-def exemption keys off the variable floor instead of the kind; S1–S8 scoping pins retargeted (S8: dynamic `VLA(−32,8)`-equivalent becomes floored Range, static converts); C4/R11 merge rows extended. No emitter changes.

**Done when:** `alloca_vla` converts ≥1 disjoint region with byte-identical stdout (or precisely part-documents why, per the amended VB-05 fallback); suite green.
