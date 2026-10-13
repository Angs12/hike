# Pins: Cbat_clp.Pieces

Module `Cbat_clp.Pieces`. One row per pin in `test/unit/test_pieces.ml`.

Except PCS-09 through PCS-14's observed failures, red evidence is by review; the disable
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
| PCS-14 | a directional ray's translate contains every shifted element: an ordered image keeps the ray to its edge, a wrapped image is the exact progression | restore the per-direction base-wrap guards in `Cbat_clp_core.translate` | observed FAIL before the correction (`PCS-14.exhaustive` at width 8); the full descending stack class `+ 8` collapsed to `{0}` and broke `tls_initialized` at gcc O2/O3 with protection |
| PCS-15 | the canonical merge: union/intersection/diff outputs stay ordered and sound over random progressions (the merge paths, no re-sort) | replace `merge_sorted` with `List.append` (the union merge degenerates to an append) | observed FAIL at `canonical:min-order` under that inversion (2026-10-13; PCS-16 also FAILs) |
| PCS-16 | the union merge is a linear merge: disjoint spans keep every piece, operand order does not matter, and re-union is idempotent | drop the fold/cap in `union` (return the raw append) | observed FAIL under that inversion (2026-10-13) |
