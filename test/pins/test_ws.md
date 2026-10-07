# Pins: Cbat_clp_set_composite

Module `Cbat_clp_set_composite`. One row per pin in `test/unit/test_ws.ml`.

Red evidence is by review: the pinned mechanisms live in the vendored
domain library and are not reachable from a test seam, so the disable
recipe is the textual inversion of the pinned contract recorded below.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| WS-01 | W7: the FinSet diffs — exact; the mixed-width pair shares no elements | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-02 | W8: the Clp\FinSet — the boundary-touch run removed exactly: [0,10] \ {0,1,2} = {3..10} | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-05 | D1-5: composite meet on width-mismatched sets -> no assert, not bottom | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-07 | D5-6: composite rshift on mixed-width CLPs COMPUTES (lane A) — non-top, no assert | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-10 | property WordSet.overlap vs meet is_bottom (7 sampled pairs) | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-13 | property m6 overlap = not is_bottom o meet enumerated (300 random equal-width trials, representation-aware) | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-14 | CARDN-W1: the \|segment\|*\|offs\| product saturates past the exact threshold | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-15 | PW-S1: a singleton stack address's extrema are the exact address | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-17 | PW-B1: an AND confined to the certified nibble computes the ABI truth | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-32 | DOM-44: a blind stack binop keeps the wider operand width | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-33 | UT1-42: the composite mixed-step meet is EXACT — {10,12,14,16,18} ∩ {16,17,18,19} = {16,18} | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-34 | the disjoint union: two case targets stay two pieces — {0,100} never hulls into [0,100] | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-35 | the wrapped SP piece measures — a stack value whose offsets wrap the modulus keeps signed extrema and segment-relative bounds (-16, 16) instead of answering None | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-36 | a symbolic stack top is not the lattice top (`equal` vs `is_top`): the segment hull is a value, not `⊤` | answer `is_top` for a stack-symbolic hull | pin FAILs: the symbolic top reads top |
| WS-37 (C5 commit A, lane vsa-generality) | an all-ones 64-bit mask is the identity on the stack line: `round_down_image` at `s ≥ 64` returns the offsets (the old `block o = o − (stack_base + o) = −stack_base` singleton excluded the true image — the latent unsoundness, reachable only from `and rsp, -1`) | revert `round_down_image`'s `s ≥ 64` early-out to the `m64 = −1L` block computation | the image reads the `−stack_base` singleton instead of the input band `[8,40]` (demonstrated red 2026-10-01 before the fix landed) |
| WS-38 | joining or widening a relative value with an originless numeric twin loses the origin and retains both values | infer an origin from the numeric stack band | the joined value incorrectly retains Stack |
| WS-39 (lane remaining-plan A6) | `widen_join` keeps a two-piece value's hole under a growing widen: `hull_join`'s plain case pairs the two piece unions piece-aligned (`P.widen_join`) when both sides carry one, so the interior exclusion survives instead of being hulled shut; every other plain shape widens the hull. | make the plain arm hull the `Clp`/`Clp` case too (`Clp (P.of_progression (f (as_clp t1) (as_clp t2)))`) | the growth arm FAILs: `widen_join hole grown` includes `5` (the hole is hulled shut) |

| WS-43 | a landmark translation of two values in one module section stays in that section (`Cbat_landmarks.extrapolate` via `keep_section`), so a dispatch base keeps its `Rip` provenance through loop widening | return the plain translated interval | the extrapolated walk has no origin |
| WS-42 | a singleton adjacent to a run canonicalizes into that run (`Pieces.adjacent_merge`), so a section-relative pointer walk widens instead of growing one byte per round | require equal non-zero steps in `adjacent_merge` | the joined walk keeps two pieces and the widen only joins |
| WS-41 | a relative piece union within the FinSet exact budget is never capped: a section-relative target set of nine irregular words (five runs) enumerates all nine | apply the 4-piece cap regardless of cardinality | the enumeration gains hull words |
| WS-40 | stack queries and memory keys use carried origins; plain, Abs and Rip values never acquire stack identity from their bits | restore numeric-band stack inference | originless floating-point bits become stack pointers |
