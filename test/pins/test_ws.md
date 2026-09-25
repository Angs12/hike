# Pins: Cbat_clp_set_composite

Module `Cbat_clp_set_composite`. One row per pin in `test/unit/test_ws.ml`.

Red evidence is by review: the pinned mechanisms live in the vendored
domain library and are not reachable from a test seam, so the disable
recipe is the textual inversion of the pinned contract recorded below.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| WS-01 | W7: the FinSet diffs — exact; the mixed-width pair shares no elements | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-02 | W8: the Clp\FinSet — the boundary-touch run removed exactly: [0,10] \ {0,1,2} = {3..10} | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-03 | W8b: the Clp\FinSet interior run — EXACT: [0,10] \ {3,4,5} = [0,2] ∪ [6,10] (the piece diff) | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-04 | W8c: the Clp\FinSet with gaps — EXACT: [0,10] \ {3,5} keeps its pieces (never hulls) | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-05 | D1-5: composite meet on width-mismatched sets -> no assert, not bottom | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-06 | D1-6: composite meet on matching widths is still exact | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-07 | D5-6: composite rshift on mixed-width CLPs COMPUTES (lane A) — non-top, no assert | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-08 | D5-7: composite arshift on mixed-width CLPs COMPUTES (lane A) — non-top, no assert | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-09 | D5-8: composite rshift on same-width singletons still exact | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-10 | property WordSet.overlap vs meet is_bottom (7 sampled pairs) | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-11 | property WordSet.overlap width-mismatch → false (pinned convention, FinSet/FinSet) | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-12 | property WordSet.meet width-mismatch → wider operand (non-bottom) | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-13 | property m6 overlap = not is_bottom o meet enumerated (300 random equal-width trials, representation-aware) | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-14 | CARDN-W1: the \|segment\|*\|offs\| product saturates past the exact threshold | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-15 | PW-S1: a singleton stack address's extrema are the exact address | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-16 | PW-S2: an offset interval projects to its exact address hull | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-17 | PW-B1: an AND confined to the certified nibble computes the ABI truth | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-18 | PW-B2: a shift keeps unknown bits and answers top | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-19 | PW-B3: an extract confined to the certified nibble computes | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-20 | PW-B4: a wide low cast keeps unknown bits and answers top | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-21 | PW-B5: add keeps the stack shape with exact offsets | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-22 | PW-B6: plain singletons keep the exact bitwise AND | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-23 | PW-R1: the certified AND answers the true residue | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-24 | PW-R2: a sub-nibble mask keeps its bits | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-25 | PW-R3: a certified extract answers the masked bits | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-26 | PW-R4: a certified narrow cast answers the low bits | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-27 | PW-R5: a certified AND over an offset interval answers the residue hull | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-28 | PW-R6: a bit-op past the enumeration budget answers top | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-29 | PW-R7: an unconfined mask keeps fabricated bits and answers top | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-30 | PW-R8: two stack addresses' AND answers top | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-31 | PW-R9: a HIGH cast keeps the unknown bits and answers top | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-32 | DOM-44: a blind stack binop keeps the wider operand width | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-33 | UT1-42: the composite mixed-step meet is EXACT — {10,12,14,16,18} ∩ {16,17,18,19} = {16,18} | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
| WS-34 | the disjoint union: two case targets stay two pieces — {0,100} never hulls into [0,100] | textually invert the pinned contract in `Cbat_clp_set_composite` | pin FAILs under that inversion (re-demonstrated by review) |
