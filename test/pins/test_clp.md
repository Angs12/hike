# Pins: Cbat_clp

Module `Cbat_clp`. One row per pin in `test/unit/test_clp.ml`.

Red evidence is by review: the pinned mechanisms live in the vendored
domain library and are not reachable from a test seam, so the disable
recipe is the textual inversion of the pinned contract recorded below.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| CLP-01 | CLP1: create n is a 32-bit singleton (bitwidth/min/max/cardn) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-02 | CLP1: elem of the singleton {10} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-03 | CLP2: interval {10,12,14,16,18}: bounds sane | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-04 | CLP2: interval membership (14 in, 15 not in) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-05 | CLP2: iter enumerates the interval (descending; sorted = the set) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-06 | CLP2: cardinality equals the iter length (bounds sanity) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-07 | CLP3: of_list ~width:16 [3;1;2] -> {1,2,3} (sorted, deduped) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-08 | CLP4: of_list [] is bottom | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-09 | CLP5: bottom: cardn 0, empty iter, no min elem | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-10 | CLP6: top: is_top, not bottom, absorbs by subset | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-11 | CLP7a: create_ascending basic properties and bounds | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-12 | CLP7b: create_descending basic properties and bounds | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-13 | CLP7c: directional rays canonicalize singletons to Finite | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-14 | CLP8: join of disjoint singletons contains both operands | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-15 | CLP8: join is above its operands (precedes = subset) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-16 | CLP9: join is commutative | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-17 | CLP10: bottom is the join identity (both orders) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-18 | CLP11: top absorbs in join | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-19 | CLP19: join of equal single points is the point | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-20 | CLP12: meet of overlapping intervals: intersection members only | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-21 | CLP13: top is the meet identity; bottom is the meet zero | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-22 | CLP14: meet absorption: (p U q) n p = p | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-23 | CLP15: meet of disjoint single points is bottom | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-24 | CLP16: single-point meet: {10} n {10,12,14,16,18} = {10} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-25 | CLP17: meet is below join | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-26 | CLP18: widen_join p p = p; widen_join bottom {5} = top | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-27 | W1: [0,9] \ [3,5] — the interior run is two pieces, not one CLP: the identity (the sound over-approximation) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-28 | W1b: the boundary-touch runs are exact — [0,9] \ [0,2] = {3..9}; [0,9] \ [7,9] = {0..6} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-29 | W2: full64 \ {0x2a} = the wrapped complement (cardn 2^64 − 1, exact) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-30 | W3: the bottom/absorption — diff bottom a = bottom; diff a bottom = a; diff a a = bottom; the singleton cases | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-31 | W4: the diff contract — (diff a b) ∩ b = ∅ element-wise; diff ⊆ a; a\b ⊆ diff | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-32 | W5: the gapped subtraction is the identity — {0,2,4,6,8} \ {0,4,8} = {0,2,4,6,8} (not a run) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-33 | W6: the singleton removal — the boundary singletons exact ([0,10] \ {0} = {1..10}; \ {10} = {0..9}); the interior singleton is the identity | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-34 | W9: lnot/neg — the exact mirror rows: lnot {0,2,4} = {7,5,3}; neg {0,2,4} = {0,6,4}; the top fixed; the singleton mirrors | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-35 | P5: not_implemented ~top degrades to top without raising | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-36 | P5: not_implemented without a top still raises NotImplemented | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-37 | P5: the top-path hit emits a warning log line (section cbat_vsa) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-38 | A1: meet wrap {10..18} n {16..19} is NOT bottom (live path) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-39 | A1: ... and still contains the true intersection {16,18} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-40 | A1: ... it is the wider operand {10,12,14,16,18} (over-approx) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-41 | A2: wrap {3,4,5} n {0,2,4} not bottom, contains 4 | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-42 | A3: genuinely disjoint meets are still bottom (unchanged) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-43 | A3: bottom is still the meet zero; top the meet identity | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-44 | D3-1: div by a set containing 0 -> top, no raise | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-45 | D3-2: sdiv by a set containing 0 -> top, no raise | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-46 | D3-3: div by exactly {0} -> the word semantics (x/0 = ones) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-47 | D3-4: sdiv by exactly {0} -> the word semantics (x/0 = ones) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-48 | D3-5: div by a nonzero singleton still computes (no regression) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-49 | D2-1: CLP widen_join of non-subset singletons -> join, no assert | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-50 | D2-2: CLP widen_join of equal inputs is still the input | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-51 | D2-3: CLP widen_join of a subset pair still widens (bottom {5} -> top) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-52 | EX1b: the extrapolation contains the join (soundness) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-53 | EX3: widen_join sound | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-54 | EX4: widen_join idempotent | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-55 | EX5: widen_join sound | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-56 | EX6: widen_join sound | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-57 | O4c-1: width-64 singleton 0xFFFF_FFFF_FFFF_FFFF is unsigned — min = max = itself, elem holds, 0 not in | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-58 | O4c-2: top 64 is the 2^64-cardinality class — is_top/is_infinite, absorbs a singleton (the Big fallback, not I64-truncated) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-59 | O4c-3: top 63 is the 2^63-cardinality class (fits Int64 — the I64 boundary) — is_top/is_infinite | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-60 | O4c-4: width-63 singleton 2^63−1 is unsigned and exact (top bit of a 63-bit word; min = max = itself) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-61 | O4c-5: 64-bit wrap add — {0xFFFF_FFFF_FFFF_FFFF} + {1} = {0} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-62 | O4c-6: 63-bit wrap sub — {0} − {1} = {2^63 − 1} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-63 | O4c-7a: add commutative | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-64 | O4c-7b: meet commutative | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-65 | O4c-7c: join commutative | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-66 | O4c-7d: meet idempotent | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-67 | O4c-8: step 0 with cardn 1 canonizes to the singleton {10} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-68 | O4c-9: cardn 0 is bottom (empty iter, no min) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-69 | O4c-10: cardn-2 wrap flips the pair to ascending order (min 0xFFFFFFEE, max 0xFFFFFFF0) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-70 | O4c-11: step·cardn = 2^w (2·4 = 8 = 2^3) is infinite — {0,2,4,6}, cardn 4, 7 not in | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-71 | O4c-12: R2-1 — meet {0..8} with the circular hull {0xFFFFFFFF,0..8} = {0..8} exactly (no spurious 0xFFFFFFFF) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-72 | A-1: mixed-width rshift (32-bit {0xFF} >> 64-bit {2}) is EXACTLY {0x3F} at 32 bits (no guard fire) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-73 | A-2: the 252-hit shape (32-bit >> 64-bit [0,40)) — the coerced three-way split yields a non-top, non-bottom result | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-74 | A-3: mixed-width rshift overshift (32-bit >> 64-bit {40}) is EXACTLY {0} at 32 bits | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-75 | A-4: mixed-width arshift sign-fill (32-bit {all-ones} arshift 64-bit {40}) is EXACTLY {all-ones} at 32 bits (the SIGN-extension) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-76 | A-5: the antipodal overshift image (64-bit {1, 2^63} arshift {70}) is {0, all-ones} (equal-width path, no coercion) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-77 | D5-1: CLP rshift on mixed-width operands COMPUTES (lane A) — {0} exactly, no assert, no top | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-78 | D5-2: CLP arshift on mixed-width operands COMPUTES (lane A) — {0} exactly, no assert, no top | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-79 | D5-3: CLP rshift/arshift on same-width singletons still exact | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-80 | D5-4: rshift by an amount >= the operand width -> {0} exactly (overshift=zero, no raise) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-81 | D5-5: rshift by an amount < the operand width still computes | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-82 | D7-10: lshift 2-bit {2} amount vs 64-bit operand -> computes {64}, no spurious fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-83 | D7-11: lshift overshift (6-bit {40} amount vs 32-bit operand) -> {0} exactly, no fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-84 | D7-12: rshift 2-bit {2} amount vs 64-bit operand COMPUTES {4} (lane A), wrapped guard never fires | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-85 | D7-13: arshift 2-bit {2} amount vs 64-bit operand COMPUTES {4} (lane A), wrapped guard never fires | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-86 | D7-14: rshift/arshift overshift ({40} vs 32-bit) -> {0} exactly, no fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-87 | E2eC-1: lshift {16} by {64} (min >= width) -> EXACTLY {0}, no fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-88 | E2eC-2: lshift {16} by multi-card overshift {64,68,72} stride 4 -> {0}, no fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-89 | E2eC-3: rshift {16} by {64} (min >= width) -> EXACTLY {0}, no fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-90 | E2eC-4: arshift overshift of a mixed-sign operand -> {0, all-ones}, no fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-91 | E2eC-5: arshift overshift of a nonneg operand -> {0} exactly (sign-extension) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-92 | E2eC-6: arshift overshift of a negative operand -> {all-ones} exactly | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-93 | E2eC-7: lshift {16} by straddling [8,70] step 2 -> non-top, contains capped image ∪ {0} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-94 | E2eC-8: rshift {2^40} by straddling [8,70] step 2 -> non-top, contains capped image ∪ {0} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-95 | E2eC-9: arshift {2^63} by straddling [8,70] step 2 -> non-top, contains capped base ∪ {all-ones} | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-96 | E2eC-10: lshift {16} by top(64) amount -> stride-class result (non-bottom, contains 0 and 16), no fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-97 | E2eC-11: array_local pattern — 32-bit operand shifted by {32} -> {0} exactly, no fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-98 | E2eC-12: array_local pattern — 8-bit operand shifted by {8} -> {0} exactly, no fire | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-99 | property Clp->FinSet->Clp round-trip (sampled progressions) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-100 | property m6 FinSet↔Clp round-trips enumerated (200 random progression trials: soundness always, exactness on wrap-free arcs) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-101 | PBH-M1: mod of a wide interval by a constant is the residue hull | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-102 | PBH-M2: mod inside one quotient block is the exact sub-interval | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-103 | PBH-M3: mod at width 128 (the idiv concat) keeps the residue bound | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-104 | PBH-M4: mod by exactly {0} is the identity (word semantics) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-105 | PBH-M5: mod by a bounded divisor range caps at its max | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-106 | PBH-M6: mod by strictly larger divisors keeps the dividend | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-107 | PBH-M7: smod of a nonnegative interval is the residue hull | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-108 | PBH-M8: smod of a mixed-sign interval stays within +-(k-1) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-109 | PBH-M11: sdiv corner hull soundness sweep (signed dividends, k<=5) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-110 | PBH-M9: mod/smod row soundness sweep (widths 4..8, all intervals, k<=5) | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
| CLP-111 | PBH-M10: same-quotient mod results are the exact residue hull | textually invert the pinned contract in `Cbat_clp` | pin FAILs under that inversion (re-demonstrated by review) |
