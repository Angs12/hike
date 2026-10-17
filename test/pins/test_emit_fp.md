# Pins — test_emit_fp

Module: `test/unit/test_emit_fp.ml` (group `emit_fp`, ids `FP-01`, `FP-32`, `FP-33`, `FP-35`),
migrating `test_cbat/test_fp.ml`.  Every source `check` site is carried; none
retired.

Production mechanisms: `src/bil2llvm_fp.ml` (`native_fp_table`, `native_fp_op`,
the `fp_sig` interface, the render arms of `create_native_fp_call`) and
`src/bil2llvm_calls.ml` (`create_call`'s mapping branch and its unmapped-intrinsic
warning).  The 29-row native-FP execution table is one pin per row: the map
assertion and the emission assertion live in the same pin, so a dropped row is
exactly one red pin (the recorded FP-table incident — a merge silently dropped
11 of 26 rows).

There is **no `Test_seam`** for the emitter, so no switch can be
flipped from the test tier.  Production `src/` is never modified; the disable
recipes below are textual, and the recorded red is re-demonstrated by review
whenever the cited mechanism changes.  Every pin builds its own fixture inside
its closure — no cross-pin state.

| id | mechanism | disable recipe | red evidence |
| --- | --- | --- | --- |
| FP-01 | Every native-FP intrinsic the lifter emits (add/sub/mul/div/rem, forder and is_nan with and without `rne`, the widthed and unwidthed names, the casts, `hlt`) maps to its constructor through `native_fp_op` and emits its native instruction (`hike_native_fp.ml` `native_fp_table`; the render arms). The names are spelled out in the pin, so a dropped row is a red. | Delete any row from `native_fp_table`. | `check_bound` red (None) for that name. |
| FP-32 | A caller of an unmapped intrinsic name is a loud failure at emission — the external-emission fallback is deleted (the atomic lane), so no module carries a silent external intrinsic call. | Restore a warn-and-external arm in `create_call`'s `is_intrinsic_name` branch. | FP-32 FAILs: `emit_ir` returns without raising "unmapped intrinsic call". |
| FP-33 | `SFLOAT`'s source width is the operand value's own LLVM type: a `[:u64]` load gives `sitofp i64`, a `[:u32]`-shaped one gives `sitofp i32` (no name/spill-slot test). | In the `SFLOAT` arm, coerce the operand to i32 before `build_sitofp` (`bil2llvm_fp.ml:160-166`). | `check "FP-GPR: a [:u64] load feeds sitofp i64 …"` red: both bases emit `sitofp i32`. |
| FP-35 | A converted operand temp routes through the memory dispatch: its load uses a real pointer address (the residue alloca GEP), never `inttoptr` (raw model lane). | In `create_native_fp_call`'s `arg_value`, replace the tagged `Some d -> mem_access … (Def.rhs d)` arm with `create_exp … (Bil.Var av)` (`bil2llvm_fp.ml:146-150`). | `check "FP-OPERAND: a region-mem operand load uses a real pointer address …"` red: the load reads the raw model lane. |
