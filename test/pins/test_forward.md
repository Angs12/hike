# Pins — test_forward

Module: `test/unit/test_forward.ml` (group `forward`, ids `FWD-01`…`FWD-18`),
migrating `test_cbat/test_forward.ml`.  Every source `check` site outside the
Call_effects family is carried as one pin; none retired.  The `CE1`…`CE10`
source checks are owned by `test/unit/test_call_effects.ml` and are not
duplicated here.

Mechanism: the forward-denotation seam `Cbat_vsa.Test_seam`
(`denote_def` / `denote_defs` / `denote_imm_exp` / `reachable_jumps`) over BIR
fixtures, plus the image-backed load arm (`Cbat_transfer.denote_exp`'s
`section_images_ref`) and the certified-nibble bit-op rule
(`Cbat_clp_set_composite`).  Every pin builds its own fixture inside its
closure; the image pins arm and disarm `Vsa.set_section_images` through
`Harness.protect`, so no state crosses pins.

The forward rules are not Test_seam-switchable (no disable flag exists), so —
per the lane spec §Fail-before — the disable recipes below are textual and
name the production site to break; the recorded red is the state that recipe
produces (re-demonstrated whenever the cited mechanism changes).  Production
`src/` is never modified.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| FWD-01 | `denote_exp`'s `Bil.Ite` arm joins both branch values, so a `{0,1}` flag does not kill the else value. | In `src/cbat_vsa/cbat_transfer.ml`, make the `Bil.Ite` arm denote only the then-branch (`denote_exp t env`, no union with the else arm). | FWD-01 FAILs: `{20}` is absent from the result. |
| FWD-05 | A store through a non-singleton/top address invalidates the whole memory (whole-memory top), never preserving the pre-store cells. | In `cbat_transfer.ml`'s Store transfer, route a non-singleton address to the preserved memory (return the old memmap) instead of `Mem.top`. | FWD-05 FAILs: `mem2` equals the preserved `mem1`, not `Mem.top`. |
| FWD-07 | The `EQ` transfer over a non-singleton `{0,1}` operand answers bool_top `{0,1}` (cardn 2), never bottom. | In `cbat_transfer.ml`, make the comparison arm return `WordSet.bottom` when an operand is non-singleton. | FWD-07 FAILs: `Ws.is_bottom` true (or cardn ≠ 2). |
| FWD-08 | A lifted 1-bit flag (`val_top (Imm 1)`) denotes `{0,1}` with cardn 2, not bottom. | In `cbat_transfer.ml`, make `val_top (Type.Imm 1)` return bottom instead of `{0,1}`. | FWD-08 FAILs: `is_bottom` true / cardn 0. |
| FWD-09 | Overlapping comparisons (`LT` over two top64 operands; `EQ(0, top64)`) answer bool_top `{0,1}`, not bottom. | Make the comparison arm return bottom on an overlap it cannot decide. | FWD-09 FAILs: `ok_lt`/`ok_eq` false. |
| FWD-10 | `reachable_jumps` keeps a jump whose cond may be true (`{0,1}` flag) and threads fall-through; no unsound pruning of a may-take edge. | In `cbat_transfer.ml`, make `reachable_jumps` drop a jump when its cond is non-singleton (`if not (is_singleton cond) then Skip`). | FWD-10 FAILs: `kept` is empty (or the loop body state loses the flag). |
| FWD-11 | The image arm of `denote_exp`'s Load reads the exact section words for a hull fully inside a threaded image. | In `cbat_transfer.ml`, make the image arm return `None` (never consult `section_images_ref`). | FWD-11 FAILs: the load stays abstract top. |
| FWD-12 | With no threaded images (`section_images_ref = []`) the image arm is not entered — the load keeps its abstract value. | Make the arm synthesize a fabricated image when `images = []` (e.g. answer a singleton word instead of `None`). | FWD-12 FAILs: the result is not top. |
| FWD-13 | The image arm refuses a hull that overhangs the image's end (`last > img_hi`), keeping the abstract value. | Drop the arm's end-span test (`last <= img_hi` → `true`) and make `image_word` answer zero for an out-of-range offset. | FWD-13 FAILs: the result is a bounded set, not top. |
| FWD-14 | A stored cell in range wins over the image bytes (the `Mem.has_cell_in` guard refuses the arm). | In `cbat_transfer.ml`, drop the `Mem.has_cell_in` guard so the image bytes override the stored cell. | FWD-14 FAILs: the result is the image word (`0x2d`), not `{0x12345678}`. |
| FWD-15 | The certified-nibble bit-op rule makes the movaps alignment guard (`(RSP−0x48) & 0xF == 0`) denotate the exact singleton `{1}` — the #GP path is provably dead. | In `src/cbat_vsa/cbat_clp_set_composite.ml`, set `certified_bits = 0` (the AND becomes blind and answers top). | FWD-15 FAILs: top contains `0` too, so `elem 0` is true. |
| FWD-16 | A width-mismatched equality is the coercer's contract violation: the domain answers top — the one-bit `{0,1}` — never a coerced comparison. | In `cbat_transfer.ml`'s `denote_binop`, coerce the operands (cast to the common width + recurse) instead of the identity. | FWD-16 FAILs: the result is the coerced `{1}` (or a definite `{0}`). |
| FWD-17 | A concat keeps its operands' order across representations: the composite's mixed FinSet/Clp pair passes the Clp operand first only when it WAS first, so `Concat({0}, top64)` is the low-64 range `[0, 2^64-1]` — never the high-64 multiples `{k·2^64}`. | In `cbat_clp_set_composite.ml`'s `op_pair`, merge the mixed pair back into one or-pattern `Ps ps, Fs s \| Fs s, Ps ps -> binop_pieces op ps (pieces_of_finset s)` (the Clp operand always first). | FWD-17 FAILs: `1` is absent from the result (the swapped high-64 set). |
