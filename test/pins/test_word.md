# Pins: Cbat_word

Module `Cbat_word` (`src/cbat_vsa/cbat_word.ml`), pinned by
`test/unit/test_word.ml` (ids `WORD-…`).

Red evidence is by review: the pinned mechanisms live in the vendored
domain library and are not reachable from a test seam, so the disable
recipe is the textual inversion of the pinned contract recorded below.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| WORD-05 | WO5: lead_1_bit | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-07 | WO7: gt_int | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-08 | CAST-W1: a negative 32-bit word's SIGNED cast to 64 sign-extends | textually invert the pinned contract in `Cbat_word` | pin FAILs under that inversion (re-demonstrated by review) |
| WORD-09 | N4: signed/unsigned return the word itself when the flag already matches | rebuild the word unconditionally in `Cbat_word.signed` / `unsigned` | pin FAILs (physical equality) with the early-return arms removed |
