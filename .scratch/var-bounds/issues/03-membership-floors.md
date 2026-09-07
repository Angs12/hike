# VB-03 — Membership emits variable floors (light-up)

**Status:** done (merged cdfe1cc 2026-09-04; 585 ok / 0 FAIL; VLA kind producer-less)
**Depends on:** VB-01
**Blocks:** VB-04

**What to build:** the classify-time shared-variable verdict emits `Range(anchor-s, anchor)` instead of the VLA kind (verdict logic otherwise verbatim; finite cap dropped, uncapped extent is the sound rule). The V1–V29 membership pins stay green through the rewrite (retargeted to floors); V29 spill end-to-end must still resolve. No emitter changes.

**Done when:** dynamic addresses tag variable-floored Range; suite green; diagnostics change only where addresses genuinely resolve.
