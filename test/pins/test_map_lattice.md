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
| MAP-30 | a read that starts inside a wider point cell extracts the bytes at its offset (the high dword and byte 1 of a stored qword), when that cell is the sole overlap | drop the `containing_cell` fallback from `Mem.find'` | pin FAILs: the high dword and byte reads answer top |
| MAP-27 | a write wider than the word is one cell per word: a 128-bit stack store reads back as two words (the code word keeps its origin) and as one 128-bit value. | textually invert the pinned contract in `Cbat_ai_memmap` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-28 | a strided read is the join of its grid points: each grid point a word cell joins exactly; a point with no cell makes the read top. | textually invert the pinned contract in `Cbat_ai_memmap` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-29 | a read narrower than its cell is the bytes at the cell's start. | textually invert the pinned contract in `Cbat_ai_memmap` | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-31 | wrapped candidate queries deduplicate a spanning cell and preserve origin filtering for reads and stores near zero | concatenate wrapped query results without deduplication, or remove the same-origin query filter | pin FAILs under that inversion (re-demonstrated by review) |
| MAP-32 | `precedes` checks the right map's cells against the left map's gaps and cells (an empty map does not precede a fact-bearing one) | query `m2` instead of `m1` in the second loop of `precedes'` | observed FAIL before the fix at `MAP-32.top-vs-fact` (2026-10-15) |
| MAP-33 | `join m m` and `meet m m` return `m` physically; distinct maps still rebuild | remove the `same_tree` shortcut in `Cbat_ai_memmap.join` / `meet` | MAP-33.join and MAP-33.meet FAIL (physical identity) |
