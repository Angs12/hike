# Pins: Cbat_clp.Pieces

Module `Cbat_clp.Pieces`. One row per pin in `test/unit/test_pieces.ml`.

Except PCS-09 through PCS-13's observed failures, red evidence is by review; the disable
recipes invert the pinned contracts in the vendored domain library.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| PCS-01 | the canonical form: sorted, disjoint, constant-difference runs, contained pieces dropped, adjacent same-step runs merged | drop the merge/drop arms of `insert` in `Cbat_clp.Pieces` | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-04 | the cap: five pieces hull to four by the smallest growth, sound | pick an arbitrary pair in `choose_pair` | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-05 | the positional widen: stable pairs widen, excess hulls into the last, a top pair collapses | drop the excess-hull arm of `positional` | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-06 | the union-order precedes: one covering piece or element-wise coverage | replace `precedes` with hull containment | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-08 | the parts exactness: a straddling lshift keeps the overshift and the capped exact pieces apart | collapse the parts in `Pieces.lshift` | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-09 | growing excess pieces enter the last pair before both widening and landmark extrapolation | coalesce excess pieces into the already-widened result | observed FAIL on the pre-fix code (`PCS-09.widen`); Clang O1 `rodata_strings` also timed out |
| PCS-10 | strided meets solve the integer grid before clipping to word bounds, including an oversized period | restore modular Bezout arithmetic in the meet solver | observed FAIL before the correction at widths 8, 16, 32 and 64 |
| PCS-11 | correct grid overlap keeps disjoint pieces separate through normalization, order and extrapolation | restore modular grid arithmetic used by `overlap_exact` | observed FAIL at `PCS-11.canonical` before the correction |
| PCS-12 | subset checks each source arc, including new alignments introduced by rotation | compare only the reduced endpoints | observed FAIL before the correction; sparse wrapped containment and ray alignment are also covered |
| PCS-13 | directional membership, enumeration and complement denote the same bounded grid | treat rays as circular in `nearest_pred` and traverse descending rays from their upper bound | observed FAIL at `PCS-13.desc` before the correction |
