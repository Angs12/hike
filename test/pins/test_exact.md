# Pins: Cbat_clp.Exact

Module `Cbat_clp.Exact` (formerly `Cbat_fin_set`, superseded by ADR 0031, T27 step 2). One row per pin in `test/unit/test_exact.ml`.

Red evidence is by review: the pinned mechanisms live in the vendored
domain library and are not reachable from a test seam, so the disable
recipe is the textual inversion of the pinned contract recorded below.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| FS-01 | FS1: of_list basics (cardn/bitwidth/min/max/elem) | textually invert the pinned contract in `Cbat_clp.Exact` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-03 | FS2: lift1 unops are involutive (neg, lnot) | textually invert the pinned contract in `Cbat_clp.Exact` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-04 | FS3: lift2 union/intersection | textually invert the pinned contract in `Cbat_clp.Exact` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-08 | FS7: add: {1,2} + {10} = {11,12} | textually invert the pinned contract in `Cbat_clp.Exact` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-09 | FS8: extract/cast/concat width sanity | textually invert the pinned contract in `Cbat_clp.Exact` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-10 | FS9 (delta #1): equal on width-mismatched sets is false (no assert) | textually invert the pinned contract in `Cbat_clp.Exact` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-11 | image producers emit ascending distinct unsigned arrays across Small/W64/Big, including nonmonotone bit images | reverse the Patricia branch emission or retain duplicate leaves | explicit expected order/count and concrete XOR membership reject the inversion |
