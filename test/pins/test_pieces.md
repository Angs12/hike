# Pins: Cbat_clp.Pieces

Module `Cbat_clp.Pieces`. One row per pin in `test/unit/test_pieces.ml`.

Red evidence is by review: the pinned mechanisms live in the vendored
domain library and are not reachable from a test seam, so the disable
recipe is the textual inversion of the pinned contract recorded below.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| PCS-01 | the canonical form: sorted, disjoint, constant-difference runs, contained pieces dropped, adjacent same-step runs merged | drop the merge/drop arms of `insert` in `Cbat_clp.Pieces` | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-04 | the cap: five pieces hull to four by the smallest growth, sound | pick an arbitrary pair in `choose_pair` | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-05 | the positional widen: stable pairs widen, excess hulls into the last, a top pair collapses | drop the excess-hull arm of `positional` | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-06 | the union-order precedes: one covering piece or element-wise coverage | replace `precedes` with hull containment | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-08 | the parts exactness: a straddling lshift keeps the overshift and the capped exact pieces apart | collapse the parts in `Pieces.lshift` | pin FAILs under that inversion (re-demonstrated by review) |


