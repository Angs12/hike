# Pins — test_emit_fp

Module: `test/unit/test_emit_fp.ml` (group `emit_fp`, ids `FP-01`…`FP-35`),
migrating `test_cbat/test_fp.ml`.  Every source `check` site is carried; none
retired.

Production mechanisms: `src/bil2llvm_fp.ml` (`native_fp_table`, `native_fp_op`,
the `fp_sig` interface, the render arms of `create_native_fp_call`) and
`src/bil2llvm_calls.ml` (`create_call`'s mapping branch and its unmapped-intrinsic
warning).  The 29-row native-FP execution table is one pin per row: the map
assertion and the emission assertion live in the same pin, so a dropped row is
exactly one red pin (the recorded FP-table incident — a merge silently dropped
11 of 26 rows).

There is **no `Test_seam`** for the emitter, so no fail-before switch can be
flipped from the test tier.  Production `src/` is never modified; the disable
recipes below are textual, and the recorded red is re-demonstrated by review
whenever the cited mechanism changes.  Every pin builds its own fixture inside
its closure — no cross-pin state.

| id | mechanism | disable recipe | red evidence |
| --- | --- | --- | --- |
| FP-01 | `native_fp_op "@intrinsic:fmul_rne_ieee754_binary_64" = Some FMUL`; the render arm emits `fmul`. | Delete the `fmul_rne_ieee754_binary_64` row from `native_fp_table` (`src/bil2llvm_fp.ml:17`). | `check_bound` red: `native_fp_op` returns `None`; the call degrades to an external intrinsic. |
| FP-02 | `fmul_rne_ieee754_binary_32` → `FMUL`, emits `fmul`. | Delete that row (`bil2llvm_fp.ml:18`). | `check_bound` red (None). |
| FP-03 | `fadd_rne_ieee754_binary_64` → `FADD`, emits `fadd`. | Delete that row (`bil2llvm_fp.ml:19`). | `check_bound` red (None). |
| FP-04 | `fadd_rne_ieee754_binary_32` → `FADD`, emits `fadd`. | Delete that row (`bil2llvm_fp.ml:20`). | `check_bound` red (None). |
| FP-05 | `fsub_rne_ieee754_binary_64` → `FSUB`, emits `fsub`. | Delete that row (`bil2llvm_fp.ml:21`). | `check_bound` red (None). |
| FP-06 | `fsub_rne_ieee754_binary_32` → `FSUB`, emits `fsub`. | Delete that row (`bil2llvm_fp.ml:22`). | `check_bound` red (None). |
| FP-07 | `fdiv_rne_ieee754_binary_64` → `FDIV`, emits `fdiv`. | Delete that row (`bil2llvm_fp.ml:23`). | `check_bound` red (None). |
| FP-08 | `fdiv_rne_ieee754_binary_32` → `FDIV`, emits `fdiv`. | Delete that row (`bil2llvm_fp.ml:24`). | `check_bound` red (None). |
| FP-09 | `frem_rne_ieee754_binary_64` → `FREM`, emits `frem`. | Delete that row (`bil2llvm_fp.ml:25`). | `check_bound` red (None). |
| FP-10 | `frem_rne_ieee754_binary_32` → `FREM`, emits `frem`. | Delete that row (`bil2llvm_fp.ml:26`). | `check_bound` red (None). |
| FP-11 | `forder_rne_ieee754_binary_64` → `FORDER`, emits `fcmp olt`. | Delete that row (`bil2llvm_fp.ml:27`). | `check_bound` red (None). |
| FP-12 | `forder_rne_ieee754_binary_32` → `FORDER`, emits `fcmp olt`. | Delete that row (`bil2llvm_fp.ml:28`). | `check_bound` red (None). |
| FP-13 | `is_nan_rne_ieee754_binary_64` → `ISNAN`, emits `fcmp uno`. | Delete that row (`bil2llvm_fp.ml:29`). | `check_bound` red (None). |
| FP-14 | `is_nan_rne_ieee754_binary_32` → `ISNAN`, emits `fcmp uno`. | Delete that row (`bil2llvm_fp.ml:30`). | `check_bound` red (None). |
| FP-15 | `is_nan_ieee754_binary` (unwidth'd) → `ISNAN`, emits `fcmp uno`. | Delete that row (`bil2llvm_fp.ml:31`). | `check_bound` red (None). |
| FP-16 | `is_nan_rne_ieee754_binary` (unwidth'd) → `ISNAN`, emits `fcmp uno`. | Delete that row (`bil2llvm_fp.ml:32`). | `check_bound` red (None). |
| FP-17 | `forder_ieee754_binary` (unwidth'd) → `FORDER`, emits `fcmp olt`. | Delete that row (`bil2llvm_fp.ml:33`). | `check_bound` red (None). |
| FP-18 | `forder_rne_ieee754_binary` (unwidth'd) → `FORDER`, emits `fcmp olt`. | Delete that row (`bil2llvm_fp.ml:34`). | `check_bound` red (None). |
| FP-19 | `cast_sfloat_rne_ieee754_binary_64` → `SFLOAT`, emits `sitofp`. | Delete that row (`bil2llvm_fp.ml:35`). | `check_bound` red (None). |
| FP-20 | `cast_sint_rne_ieee754_binary_64` → `SINT`, emits `fptosi`. | Delete that row (`bil2llvm_fp.ml:36`). | `check_bound` red (None). |
| FP-21 | `cast_sint_rne_ieee754_binary_32` → `SINT`, emits `fptosi`. | Delete that row (`bil2llvm_fp.ml:37`). | `check_bound` red (None). |
| FP-22 | `fconvert_rne_ieee754_binary_64` → `FCONVERT 64`, emits `fpext`. | Delete that row (`bil2llvm_fp.ml:39`). | `check_bound` red (None). |
| FP-23 | `fconvert_rne_ieee754_binary_32` → `FCONVERT 32`, emits `fptrunc`. | Delete that row (`bil2llvm_fp.ml:40`). | `check_bound` red (None). |
| FP-24 | `fmul_rne_ieee754_binary` (unwidth'd) → `FMUL`, emits `fmul`. | Delete that row (`bil2llvm_fp.ml:41`). | `check_bound` red (None). |
| FP-25 | `fadd_rne_ieee754_binary` (unwidth'd) → `FADD`, emits `fadd`. | Delete that row (`bil2llvm_fp.ml:42`). | `check_bound` red (None). |
| FP-26 | `fsub_rne_ieee754_binary` (unwidth'd) → `FSUB`, emits `fsub`. | Delete that row (`bil2llvm_fp.ml:43`). | `check_bound` red (None). |
| FP-27 | `fdiv_rne_ieee754_binary` (unwidth'd) → `FDIV`, emits `fdiv`. | Delete that row (`bil2llvm_fp.ml:44`). | `check_bound` red (None). |
| FP-28 | `frem_rne_ieee754_binary` (unwidth'd) → `FREM`, emits `frem`. | Delete that row (`bil2llvm_fp.ml:45`). | `check_bound` red (None). |
| FP-29 | `hlt` → `FHLT`, emits `unreachable`. | Delete that row (`bil2llvm_fp.ml:46`). | `check_bound` red (None); `FHLT`'s `create_interrupt` arm is not reached. |
| FP-30 | `native_fp_op "@intrinsic:not_a_real_intrinsic" = None`. | Make `native_fp_op` total with a catch-all (`Base.List.Assoc.find … |> Base.Option.value ~default:FMUL`, `bil2llvm_fp.ml:48`). | `check_bound` red: the match takes the `Some` arm. |
| FP-31 | A mapped row's emission carries no soft-float call (`fadd_64`'s IR has no `call` or no `@intrinsic:fadd`). | In `create_call`, drop the `| Some op -> create_native_fp_call …` arm (`src/bil2llvm_calls.ml:520`) so a mapped name falls to `create_external_intrinsic_call`. | `check "FP-TABLE fadd_64: no soft-float call survives"` red: the IR contains `call … @intrinsic:fadd…`. |
| FP-32 | A caller of an unmapped intrinsic name emits `hike: guarded: unmapped intrinsic call: …` on stderr. | Delete the `Hike_diag.warn "guarded: unmapped intrinsic call: …"` line (`src/bil2llvm_calls.ml:526-528`). | `check "FP-TABLE: an unmapped name emits the guarded warning on stderr"` red: captured stderr lacks `hike: guarded:`. |
| FP-33 | `SFLOAT`'s source width is the operand value's own LLVM type: a `[:u64]` load gives `sitofp i64`, a `[:u32]`-shaped one gives `sitofp i32` (no name/spill-slot test). | In the `SFLOAT` arm, coerce the operand to i32 before `build_sitofp` (`bil2llvm_fp.ml:160-166`). | `check "FP-GPR: a [:u64] load feeds sitofp i64 …"` red: both bases emit `sitofp i32`. |
| FP-34 | The lifter's own `[31:0]` extract (i32 value) feeds `sitofp i32` — by construction, same rule as FP-33. | In the `SFLOAT` arm, coerce the operand to i64 before `build_sitofp`. | `check "FP-GPR: the lifter's own [31:0] extract feeds sitofp i32 …"` red: the emission is `sitofp i64`. |
| FP-35 | A converted operand temp routes through the memory dispatch: a load re-pointed at `region_mem 1` GEPs `%stack_r1`, never `inttoptr` (raw model lane). | In `create_native_fp_call`'s `arg_value`, replace the tagged `Some d -> mem_access … (Def.rhs d)` arm with `create_exp … (Bil.Var av)` (`bil2llvm_fp.ml:146-150`). | `check "FP-OPERAND: a region-mem operand load GEPs its region's alloca …"` red: no `getelementptr i8, ptr %stack_r1` (the raw model lane is read). |
