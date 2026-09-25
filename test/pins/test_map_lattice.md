# Pins: Cbat_map_lattice

Module `Cbat_map_lattice`. One row per pin in `test/unit/test_map_lattice.ml`.

Red evidence is by review: the pinned mechanisms live in the vendored
domain library and are not reachable from a test seam, so the disable
recipe is the textual inversion of the pinned contract recorded below.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| MAP-01 | ML1: add on bottom stays bottom | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-02 | ML2: join_add/meet_add on bottom stay bottom | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-03 | ML3: find on bottom/top returns bottom/top | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-04 | ML4: meet/join top-bottom combos | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-05 | ML5: add then find roundtrip; missing key reads top | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-06 | ML6: join_add/meet_add merge with the stored value | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-07 | ML7: equal/precedes on small maps | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-08 | D2-4: Val.equal/precedes on idx-mismatched cells -> false (no assert) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-09 | D2-5: Val.join on idx-mismatched cells -> top fallback (no assert) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-10 | D2-6: Val.meet on idx-mismatched cells -> bottom fallback (no assert) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-11 | D2-7: Val.widen_join on idx-mismatched cells -> top fallback (no assert) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-12 | D2-8: Val ops on matching indices still work (no regression) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-13 | D2-9: Mem.widen_join of non-preceding maps -> join fallback (no assert) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-14 | D2-10: Mem.widen_join of equal maps stays equal (no regression) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-15 | opadd-a: join a key fully inside one node — interval_diff's two flanks (low flank lo 10 = {1}, middle lo 12 = {1,2}, high flank lo 19 = {1}); interval_diff returns the capped list | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-16 | opadd-b: join a key spanning several nodes — the [gaps] cells duplicate the node lo addresses, so the node lo reads are top (structural-only observation) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-17 | opadd-c1: meet a key covering the node (interval_diff `none) — the fresh gap becomes {1,2} (meet fills it); the node narrows | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-18 | opadd-c2: join a key overlapping the node's low half (interval_diff `one) — the high flank lo 16 keeps {1}; the joined cell's lo 10 is top (gap pollution) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-19 | opadd-c3: join a key overlapping the node's high half (interval_diff `one) — the low flank lo 10 keeps {1}, the joined cell lo 15 = {1,2} | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-20 | opadd-d1: a wrapped-interval WordSet fans per piece — both arcs carry the fact (lo 0 and hi 0xFFFFFFF0 = {7}), the true interior 0x50 is top | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-21 | opadd-d2: a key with hi = 0xFFFFFFFF — the finishing gap terminates at max (lo 10 = {1}; no wrapped spill at address 0) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-22 | opadd-e: the bottom map stays bottom under add/meet_add/join_add/meet_range | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-23 | opadd-f: a 64-bit {5} meets a 32-bit {5} cell via meet_poly (widened to 64, no crash) | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-24 | opadd-f2: a 64-bit {5} joins a 32-bit {5} cell -> top (the idx-mismatched join fallback), no crash | textually invert the pinned contract in `Cbat_map_lattice` | pin FAILs under that inversion (re-demonstrated by review) |
