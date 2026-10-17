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
| CLP-26 | CLP18: widen_join p p = p; widen_join (and extrapolate_steps) from bottom is the new iterate `{5}`, not top | restore `if is_bottom p1 then top (bitwidth p2)` in `Cbat_clp_core.widen_join`/`extrapolate_steps` and `[], _ -> [ C.top ] ` in `Pieces.positional` | pin FAILs under that inversion (the bottom widen is top) |
| CLP-27 | W1: [0,9] \ [3,5] — the interior run is two pieces, not one CLP: the identity (the sound over-approximation) | textually invert the pinned contract in `Cbat_clp_core.diff` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-34 | W9: lnot/neg — the exact mirror rows: lnot {0,2,4} = {7,5,3}; neg {0,2,4} = {0,6,4}; the top fixed; the singleton mirrors | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-37 | P5: not_implemented returns its top and the hit emits a warning log line (section cbat_vsa) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-38 | A1: meet wrap {10..18} n {16..19} is NOT bottom (live path) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-44 | D3-1: div by a set containing 0 -> top, no raise | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-49 | D2-1: CLP widen_join of non-subset singletons -> join, no assert | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-57 | O4c-1: width-64 singleton 0xFFFF_FFFF_FFFF_FFFF is unsigned — min = max = itself, elem holds, 0 not in | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-63 | O4c-7a: add commutative | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-67 | O4c-8: step 0 with cardn 1 canonizes to the singleton {10} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-72 | A-1: mixed-width rshift (32-bit {0xFF} >> 64-bit {2}) is EXACTLY {0x3F} at 32 bits (no guard fire) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-82 | D7-10: lshift 2-bit {2} amount vs 64-bit operand -> computes {64}, no spurious fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-100 | property m6 Exact↔Clp round-trips enumerated (200 random progression trials, widths 4/8/12/32: soundness always, exactness on wrap-free arcs) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-101 | PBH-M1: mod of a wide interval by a constant is the residue hull | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-110 | PBH-M9: mod/smod row soundness sweep (widths 4..8, all intervals, k<=5) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-112 | CAST-S1: a SIGNED extension of a set crossing the sign boundary (a finite straddle and a set across the modulus) is the element-wise image of both runs — exact, never top | restore the straddle arm's `W.msb base <> W.msb e -> [ top sz ]` in `cast_parts` | pin FAILs (result is top, or the crossing case images 144 to 144 instead of -112) |
| CLP-113 | CAST-S2: the composite's SIGNED extension of the full 32-bit domain is the two half-domains, never top | restore the `is_infinite p -> [ top sz ]` guard in `cast_parts` | pin FAILs (result is top) |
| CLP-114 | DIV-Z: `sdiv` by an exact `{0}` contains every elementwise image — a negative dividend gives `1`, a non-negative one gives `ones`, a sign-spanning one gives both | restore `sdiv_core`'s exact-zero arm to `singleton (W.ones width)` | pin FAILs (the negative dividend `{0xFF}`'s `1` is outside the result) |
| CLP-115 | AND/OR with a constant respect the operand's bounds and stride: `[0..10] & 0xff` stays `[0..10]`, `{0,8,…,800} & 0xf` is the exact `{0,8}`, `[0..100] \| 1` is the bounded odd run `{1,3,…,127}` | restore the constant arm's `create (W.zero sz) ~step:(W.one sz) ~cardn:(W.succ k)` (route no facts through `logand_general`) | pin FAILs (the interval AND answers `[0,255]`, the strided AND `[0,15]`, the OR goes top) |
| CLP-116 | modulo by a constant divisor of the stride is the base's singleton residue (`{0,8,…,800} mod 4 = {0}`, `mod 8 = {0}`, `{1,9,…} mod 4 = {1}`); a non-dividing divisor keeps the sound residue hull | drop the stride arm from `modulo_core`'s constant-divisor case | pin FAILs (the strided modulo answers `[0,3]` instead of `{0}`) |
| CLP-117 | difference by something other than one run equals the hull of its ascending survivors (`{0,2,4,6} \ {2,6}` and an equal-gap tie) | return the identity instead of the survivors' hull in `Cbat_clp_core.diff` | pin FAILs under that inversion (by review) |
