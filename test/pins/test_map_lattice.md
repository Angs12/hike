# Pins: Cbat_map_lattice

Module `Cbat_map_lattice`. One row per pin in `test/unit/test_map_lattice.ml`.

Red evidence is by review: the pinned mechanisms live in the vendored
domain library and are not reachable from a test seam, so the disable
recipe is the textual inversion of the pinned contract recorded below.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| MAP-01 | ML1: add on bottom stays bottom | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-03 | ML3: find on bottom/top returns bottom/top | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-06 | ML6: join_add/meet_add merge with the stored value | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-08 | D2-4: Val.equal/precedes on idx-mismatched cells -> false (no assert) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-13 | D2-9: Mem.widen_join of non-preceding maps -> join fallback (no assert) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-15 | opadd-a: join a key fully inside one node — interval_diff's two flanks (low flank lo 10 = {1}, middle lo 12 = {1,2}, high flank lo 19 = {1}); interval_diff returns the capped list | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-20 | opadd-d1: a wrapped-interval WordSet fans per piece — both arcs carry the fact (lo 0 and hi 0xFFFFFFF0 = {7}), the true interior 0x50 is top | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-23 | opadd-f: a 64-bit {5} meets a 32-bit {5} cell via meet_poly (widened to 64, no crash) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-25 | a top-valued `add` stores no binding (the equal-vs-top trap: `Val.top` must not be recorded as a cell) | store the cell unconditionally in `join_add` | pin FAILs: the added key is present |
| MAP-26 | the key namespace is origin-aware: a Stack cell and an Abs cell at the same numeric hull are disjoint | drop the origin from the key's `equal` | pin FAILs: the two cells merge |
