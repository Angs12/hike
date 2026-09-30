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
| WS-38 (lane vsa-union-rel) | a relative value and its plain in-band twin keep the origin through `union` and `widen_join`: the in-band plain translates into the origin's offset space, so the cell stays stack-symbolic | return `Materialise` from `rel_table`'s `Union` row for a relative/absolute pair and drop the `rel_abs` `Union` arm (`hull_join`'s `rel_plain` fallback) | the joined value reads `origin = None` (the plain hull) instead of `Some Stack` (demonstrated red 2026-09-30 before the fix landed) |
