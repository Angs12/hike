# Pins: Cbat_clp.Pieces

Module `Cbat_clp.Pieces` (and the exact run list, `Cbat_clp.Exact`). One row per pin in
`test/unit/test_pieces.ml`.

Except PCS-05/09 and the PCS-15..PCS-19 observed failures, red evidence is by review; the disable
recipes invert the pinned contracts in the vendored domain library.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| PCS-01 | the canonical form: sorted, disjoint, constant-difference runs, contained pieces dropped, adjacent same-step runs merged | drop the merge/drop arms of `merge_arc` in `Cbat_clp.Pieces` | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-04 | the tier cap (`cap_to`): five union pieces hull to four by the smallest growth, sound | pick an arbitrary pair in `choose_pair` | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-05 | the widening pairing: the overlapping couple widens, an unmatched piece stays its own atom, a top couple collapses | restore the rank pairing and the excess hull in `positional` | observed FAIL on the pre-T28 code (2026-10-14): the one-sided `{10..12}` was hulled into the first pair (`l` had 1 piece containing 5) |
| PCS-06 | the union-order precedes: one covering piece or element-wise coverage | replace `precedes` with hull containment | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-08 | the parts exactness: a straddling lshift keeps the overshift and the capped exact pieces apart | collapse the parts in `Pieces.lshift` | pin FAILs under that inversion (re-demonstrated by review) |
| PCS-09 | the overlap pairing: the old grid pairs with the first overlapping incoming piece; the disjoint excess stays its own atom (both widening and landmark extrapolation) | put the excess hull back into `positional` (coalesce each side's tail into the last pair) | observed FAIL on the pre-T28 code (2026-10-14): `widen` maxed at the ascending ray's `0xFFFFFFFF` (was `Some (ones 32)`); `extrapolate` returned `0x82` (130) instead of `0x6E` (110) |
| PCS-10 | strided meets solve the integer grid before clipping to word bounds, including an oversized period | restore modular Bezout arithmetic in the meet solver | observed FAIL before the correction at widths 8, 16, 32 and 64 |
| PCS-11 | correct grid overlap keeps disjoint pieces separate through the merge, order and extrapolation | restore modular grid arithmetic used by `overlap_exact` | observed FAIL at `PCS-11.canonical` before the correction |
| PCS-12 | subset checks each source arc, including new alignments introduced by rotation | compare only the reduced endpoints | observed FAIL before the correction; sparse wrapped containment and ray alignment are also covered |
| PCS-13 | directional membership, enumeration and complement denote the same bounded grid | treat rays as circular in `nearest_pred` and traverse descending rays from their upper bound | observed FAIL at `PCS-13.desc` before the correction |
| PCS-14 | a directional ray's translate contains every shifted element: an ordered image keeps the ray to its edge, a wrapped image is the exact progression | restore the per-direction base-wrap guards in `Cbat_clp_core.translate` | observed FAIL before the correction (`PCS-14.exhaustive` at width 8); the full descending stack class `+ 8` collapsed to `{0}` and broke `tls_initialized` at gcc O2/O3 with protection |
| PCS-15 | the canonical merge: union/intersection/diff outputs stay ordered and sound over random progressions (the merge paths, no re-sort) | replace the `merge_arc` fold in `union` with `List.append` (the union degenerates to an append) | observed FAIL at `canonical:min-order` under that inversion (2026-10-13; PCS-16 also FAILs) |
| PCS-16 | the union merge is a linear merge: disjoint spans keep every piece, operand order does not matter, and re-union is idempotent | drop the `merge_arc` fold in `union` (return the raw append) | observed FAIL under that inversion (2026-10-13) |
| PCS-17 | the exact run-list constructor keeps a nine-element five-run set exactly its elements through union, intersection, diff and to_pieces (no hull, no cap) | hull the run builder in `Cbat_clp.Exact.of_elements` to one covering progression (`Cbat_clp_core.of_list`) | observed FAIL at `PCS-17.base` under that inversion (2026-10-13): `els=[1;…;50] raw=[1;…;50] card=50 pieces=1 want [1;2;10;11;20;21;30;31;50] in 5 pieces`; constructor budget promotion also FAILs `PCS-17.union` |
| PCS-18 | a 10x10 element product is still exact: the cardinality is the concrete product count and every product is present | promote over `fin_set_size` inside `Cbat_clp.Exact.of_elements` (hull the over-budget result) | observed FAIL at `PCS-18` under that inversion (2026-10-13): `concrete=100 card=1998 elements=1998 missing=0 extra=1898` |
| PCS-19 | the nearest pairing: correspondences pair by overlap and by the smaller gap, and atoms without a counterpart stay their own pieces (rank pairing hulls across the shift) | restore the rank pairing in `positional` (pair by list index, hull the excess) | observed FAIL on the pre-T28 code (2026-10-14): both arms hulled to one piece containing 15 (`PCS-19.shift` and `PCS-19.nearest`) |
