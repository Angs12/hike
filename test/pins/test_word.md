# Pins: Cbat_word

Module `Cbat_word`. One row per pin in `test/unit/test_word.ml`.

Red evidence is by review: the pinned mechanisms live in the vendored
domain library and are not reachable from a test seam, so the disable
recipe is the textual inversion of the pinned contract recorded below.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| WORD-01 | WO1: dom_size i ~width:w = 2^i as a w-bit word (zero if w = i) | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-02 | WO2: cap_at_width keeps small words, saturates large ones | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-03 | WO3: add_exact/mul_exact widen to the exact result | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-04 | WO4: factor_2s pulls out the 2-power | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-05 | WO5: lead_1_bit | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-06 | WO6: is_one / succ_exact / lshift_exact | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-07 | WO7: gt_int | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-08 | CAST-W1: a negative 32-bit word's SIGNED cast to 64 sign-extends | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-09 | CAST-W2: a positive narrow word's SIGNED cast is the identity | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-10 | CAST-W3: a SIGNED cast to a narrower width keeps the truncated bit pattern | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-11 | WORD-BC: of_word keeps the unsigned value (all-ones stays 2^64-1) | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-12 | WORD-BC: of_word of a small word is the Small immediate | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-13 | WORD-BC: to_word of a signed negative keeps the two's-complement payload and the sign flag | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-14 | WORD-BC: to_word of a signed zero keeps the sign flag | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-15 | WORD-BC: to_word of an unsigned small value is the same bits at the same width | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-16 | WORD-BC: of_word (to_word t) is value-identity for unsigned words | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-17 | WORD-BC: the high-bit unsigned word's int64 bit pattern survives | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-18 | WORD-BC: a 80-bit word round-trips with no string path | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
