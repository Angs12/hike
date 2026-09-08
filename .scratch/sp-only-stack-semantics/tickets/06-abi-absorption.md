# Ticket 06 — ABI absorption: the frame-pointer concept leaves the record

Blocking: 05. Blocks: 07 (no hard edge — 07 is corpus work — but keep the code
tickets sequenced for clean identity attribution).

## Change (`src/hike_abi/hike_abi.ml`)

The minimality directive carried to the field. Zero intended behavior change — every
consumer was migrated at T2–T5; this ticket is the single ABI-consistency commit:

1. **`fp` field DELETED** from the record; **`callee_saved` gains RBP**
   (`[RBX;RBP;R12;R13;R14;R15]`, the SysV truth — the record's own comment already
   said "RBP carried as [fp]"). `is_fp` DELETED (zero callers after T5's tag-gate).
2. **`is_stack_reg` DELETED** (zero callers after T2/T4 — verify by grep, then
   delete; the discipline: no predicate survives without a consumer).
3. **`Abi.of_target` stops reading the target's `frame_pointer`** (`fp target`
   and its `of_target_opt` copy die).
4. **`Convutils.emit_ctx.fp` + `empty_emit_ctx`'s default DELETED** (dead since T5);
   `hike.ml`'s population site goes with it. `hike.mli`'s seam: any `fp` exposure
   dies here.
5. **`preserved_of_sub` (`cbat_vsa.ml:86-89`)** becomes `sp :: Abi.callee_saved` —
   the register SET is provably identical (`{RSP,RBP,RBX,R12..R15}` before and
   after); `test_vsa.ml`'s T4-10 pin ("RBP is preserved across the call") must
   compile and pass unchanged.
6. **The consumer grep (REQUIRED, recorded in the ticket file):** every
   `callee_saved`/`is_callee_saved` consumer whose behavior could change when RBP
   joins the list — `compute_sub_sig` (param exclusion: same result as the explicit
   fp test), `collect_sub_data` (T5's lane-keeping: already sp∪callee_saved),
   `preserved_of_sub` (identical set), DCE's keep policy (verify: `keep` uses
   return-regs/region-mem/call-regs — RBP's membership must NOT add a keep arm
   that keeps dead RBP defs; if it does, RBP stays deletable as an ordinary GPR).
   Each site: unaffected (state why) or adjusted (say how).

## Done (commit cedbb62)

- All of the above landed. **Plus the spill apparatus DELETED** (the no-gates
  ruling, which this session extended): `u32_slots_of_sub`, `cast_source_width`,
  `has_32bit_extract`, `x0_temp_name`, and the `~u32_slots` threading are gone.
- **NEW — the static model-interface table `fp_op_inputs`** (`bil2llvm_calls.ml`),
  parallel to `native_fp_op`: the mapped intrinsic name IS the interface fact, and
  `create_native_fp_call` resolves each operand from the block's `intrinsic:xN`
  temp. This REPLACED the old operand-resolution path, which consulted the argument
  signature table and fell back to the calling convention (RDI, ...) when the call
  target's sig wasn't keyed — and an undef/constant fallback operand means LLVM
  CONSTANT-FOLDS the sitofp away (no instruction, no width), so the by-construction
  `:u64`→`sitofp i64` / `31:0`→`sitofp i32` pins could not pass. The static table is
  fixture-independent and needs no sig-table games.
- **Fixture rewrites**: the two fp-gpr cast pins are genuine positives (a `:u64`
  load → `sitofp i64` for ANY base; a lifter `31:0` extract → `sitofp i32`), and
  the fp-table rows feed non-constant temps so LLVM cannot fold the op away.
- **Gates at cedbb62**: suite 516 ok / 0 FAIL; `dune runtest` ALL PASSED (clpequiv
  2,861,148 / 0 mismatches); both profiles build; corpus 32/32 rc=0; check_allocas
  160/0; semantic 32/0 at -O0 and opt -O2. IR 29/32 byte-identical vs red3-o0 —
  the only deltas are the 3 FP binaries (mixed_fp_int, union_overlap, va_arg_mixed)
  and they are ALL the one SFLOAT lane: the deleted trunc+sitofp-i32 becomes sitofp
  at the operand's own type, semantically proven.

## Gates

- `dune runtest` — T4-10 and the whole suite green; honest count.
- -O0 corpus IR byte-identity 32/32 (this ticket MUST be identity: same register
  sets everywhere, only representation changed).
- Full battery; the unit-suite fixture vocabulary (`test_common.ml`) drops any
   fp-shaped builder args mechanically.
- `grep -rn "is_fp\|is_stack_reg\|fp_of\|is_sp_or_fp\|Abi.fp\|\.fp\b" src/` — zero
  production hits (float-fp names like `is_fp_param`/`native_fp` are NOT the frame
  pointer; the grep pattern must exclude them by word shape).
