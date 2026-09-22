# Pins: Cbat_fin_set

Module `Cbat_fin_set`. One row per pin in `test/unit/test_fin_set.ml`.

Red evidence is by review: the pinned mechanisms live in the vendored
domain library and are not reachable from a test seam, so the disable
recipe is the textual inversion of the pinned contract recorded below.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| FS-01 | FS1: of_list basics (cardn/bitwidth/min/max/elem) | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-02 | FS1: singleton | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-03 | FS2: lift1 unops are involutive (neg, lnot) | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-04 | FS3: lift2 union/intersection | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-05 | FS4: join/meet are the lattice aliases of union/intersection | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-06 | FS5: precedes/equal | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-07 | FS6: bottom absorption | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-08 | FS7: add: {1,2} + {10} = {11,12} | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-09 | FS8: extract/cast/concat width sanity | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-10 | FS9 (delta #1): equal on width-mismatched sets is false (no assert) | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-11 | FS9 (delta #1): precedes on width-mismatched sets is false | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-12 | D1-1: fin_set elem on a width-mismatched word -> false (no assert) | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-13 | D1-2: fin_set overlap on width-mismatched sets -> false (no assert) | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-14 | D1-3: fin_set nearest_pred on a width-mismatched word -> None | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-15 | D1-4: intersect_generic width mismatch -> input unchanged (no assert) | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
| FS-16 | property FinSet->Clp->FinSet round-trip on small sets | textually invert the pinned contract in `Cbat_fin_set` | pin FAILs under that inversion (re-demonstrated by review) |
