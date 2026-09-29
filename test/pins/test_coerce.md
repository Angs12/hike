# Width-coercion pins (`test_coerce.ml`)

One row per pin. The pass makes every exp width-honest once, before the
VSA and the emitter read it.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| CO-03 | The fit test follows the op's signedness — an all-ones 64-bit literal narrows under `SLT`. | Use `UNSIGNED` as the fit kind in `narrow_literal` for every op. | CO-03 red: the literal does not narrow. |
| CO-04 | `0xffffffff:64` is positive under `SLT`, so the register sign-extends instead. | Fit on the raw truncation equality. | CO-04 red: the literal narrows and the comparison flips. |
| CO-05 | A comparison's result is one bit (the `exp_width` rule): an `AND` over a high-bit extract and a nested comparison is untouched. | In `exp_width`, take `max` for comparisons too. | CO-05 red: the one-bit extract casts up. |
| CO-09 | The filler follows the op's signedness — `ARSHIFT` sign-extends a narrower all-ones literal. | Make `filler_bit` always zero-fill. | CO-09 red: the widened literal is zero-extended. |
| CO-10 | `coerce_block` coerces a jmp condition. | Drop the jmp mapping in `coerce_block`. | CO-10 red: the cond keeps its 64-bit literal. |
| CO-11 | A def's value is born at its lhs's declared width — a narrower value zero-extends. | Drop the `coerce_to_lhs` wrap in `coerce_def`. | CO-11 red: the rhs stays 32-bit under a 64-bit lhs. |
| CO-14 | A store's data is exactly the store size. | Drop the data coercion in `map_store`. | CO-14 red: the data stays 64-bit under a `u32` store. |
| CO-15 | Ite branches widen to their common width. | Drop the `map_ite` widening. | CO-15 red: the 32-bit branch stays. |
| CO-16 | A phi's values are born at the phi's declared width. | Drop `coerce_phi`. | CO-16 red: the value stays 32-bit. |
| CO-17 | A Let binder's value is born at the binder's declared width. | Drop the `map_let` coercion. | CO-17 red: the bound value stays 64-bit under a 32-bit binder. |
| CO-18 | A zero-width concat operand contributes no bits — the concat reduces to the other operand (the emitter's `exp_size` rule). | Drop the zero-width rule in `map_concat`. | CO-18 red: the concat keeps both operands. |
