# Pins: Cbat_clp

Module `Cbat_clp`. One row per pin in `test/unit/test_clp.ml`.

Red evidence is by review: the pinned mechanisms live in the vendored
domain library and are not reachable from a test seam, so the disable
recipe is the textual inversion of the pinned contract recorded below.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| CLP-01 | CLP1: create n is a 32-bit singleton (bitwidth/min/max/cardn) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-09 | CLP5: bottom: cardn 0, empty iter, no min elem | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-14 | CLP8: join of disjoint singletons contains both operands | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-20 | CLP12: meet of overlapping intervals: intersection members only | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-26 | CLP18: widen_join p p = p; widen_join bottom {5} = top | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-27 | W1: [0,9] \ [3,5] — the interior run is two pieces, not one CLP: the identity (the sound over-approximation) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-34 | W9: lnot/neg — the exact mirror rows: lnot {0,2,4} = {7,5,3}; neg {0,2,4} = {0,6,4}; the top fixed; the singleton mirrors | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-35 | P5: not_implemented ~top degrades to top without raising | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-37 | P5: the top-path hit emits a warning log line (section cbat_vsa) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-38 | A1: meet wrap {10..18} n {16..19} is NOT bottom (live path) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-44 | D3-1: div by a set containing 0 -> top, no raise | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-49 | D2-1: CLP widen_join of non-subset singletons -> join, no assert | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-57 | O4c-1: width-64 singleton 0xFFFF_FFFF_FFFF_FFFF is unsigned — min = max = itself, elem holds, 0 not in | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-63 | O4c-7a: add commutative | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-67 | O4c-8: step 0 with cardn 1 canonizes to the singleton {10} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-72 | A-1: mixed-width rshift (32-bit {0xFF} >> 64-bit {2}) is EXACTLY {0x3F} at 32 bits (no guard fire) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-82 | D7-10: lshift 2-bit {2} amount vs 64-bit operand -> computes {64}, no spurious fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-100 | property m6 FinSet↔Clp round-trips enumerated (200 random progression trials, widths 4/8/12/32: soundness always, exactness on wrap-free arcs) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-101 | PBH-M1: mod of a wide interval by a constant is the residue hull | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-110 | PBH-M9: mod/smod row soundness sweep (widths 4..8, all intervals, k<=5) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-112 | CAST-S1: a SIGNED extension of a set crossing the sign boundary (a finite straddle and a wrapped progression) is the element-wise image of both runs — exact, never top | restore the straddle arm's `W.msb base <> W.msb e -> [ top sz ]` (and the whole-set element-wise image for wrapped inputs) in `cast_parts` | pin FAILs (result is top, or the wrapped case images 144 to 144 instead of -112) |
| CLP-113 | CAST-S2: the composite's SIGNED extension of the full 32-bit domain is the two half-domains, never top | restore the `is_infinite p -> [ top sz ]` guard in `cast_parts` | pin FAILs (result is top) |
