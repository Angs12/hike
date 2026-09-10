# T14 — the escape-extent rule: only a StackOff proof sizes the frame (P1)

Owner doctrine applies: architecture-side fixes (the diff deletes
cases), one mechanism, soundness over precision.
Blocked-by: **T10** (it owns `hike_vsa.ml`'s promotion rewrite right
now — this lane touches the same file's `caller_side`).
Blocks: nothing; the pin's `spill_many` member is this ticket's flip.

## The forensics (complete, byte-reconciled — the evidence)

**Fault** (gdb, `/home/tovpr/tm-battery/merge-t4b/sem-o2/
out_spill_many_lifted`): `mov %rax,0xa8(%rsp)` in `hike_main+39` —
rsp ~4 GB below the stack mapping. The prologue:
`mov $0xf5ae31c8,%eax; sub %rax,%rsp` — llc reserved a
4,121,833,928-byte frame. Nothing of the body runs.

**IR** (`emit-o2/out_spill_many.ll:13-17`):
`%frame = alloca [4121833728 x i8]`;
`%anchor = gep %frame, 0x379F0713F5AE30F8`; store to `%sp_slot`.

**The chain (four facts composing):**
1. gcc -O2 inlines `hammer` into `main` → one sub, ~30 SP-relative
   accesses spanning `[sp-176, sp+40]` (a ~224-byte frame is all it
   needs). Pre-T4 reference (`merge-t1/emit-o2-real`):
   `alloca [240 x i8]`, anchor 232, PASSES.
2. `caller_side.note_escape` (`hike_vsa.ml:147-262`) probes EVERY
   SysV int+vector param register's end state at every call block.
   At `main`'s `printf`, RCX/R9 hold gcc's scratch checksum
   arithmetic (R9 = the final `v6` = `0x6FE4483BA6456223`, verified
   by simulation; RCX an intermediate) — NOT printf arguments.
3. `in_stack_segment`'s plain-arm band (`cbat_clp_set_composite.ml:
   202-222`): a bounded signed-positive Clp with extrema ≥ 2^61 is
   re-tagged stack ("no real address lives there" — TRUE FOR
   ADDRESSES). Applied to arbitrary INTEGERS it misfires: 13/27 of
   spill_many's final values sit in `[2^61, 2^63)`.
4. `frame_dims` folds the fake extents: span = 4,007,929,975,690,637,564
   → n ≈ 4 EXABYTES; `Llvm.array_type` silently truncates the count to
   32 bits (4,121,833,728 — the deprecated unsigned binding,
   `llvm_ocaml.c:635`) while the anchor keeps the 64-bit index.

Why -O0 passes: `hammer` is call-free (no probe) and `main`'s call
passes `RDI = 173` (out of band). Why pre-T4 passed: no `note_escape`
probe of param registers.

## The fix (architecture-side, at the seam)

- **The escape-extent rule**: only a **`StackOff` denotation** (the
  symbolic-base proof — a value formed from THIS sub's SP) may
  contribute to `sp_extents`, frame sizing, and the values-served
  escape decision. A plain in-band Clp contributes NOTHING (the band
  re-tag stays for ADDRESS classification, where the argument is
  about addresses). Implement via a composite-set accessor
  (`stack_offsets : t -> Clp.t option` — answers only for `StackOff`)
  used by `note_escape` instead of `relativize_opt` (which
  deliberately serves the tag universe's smear arms).
- **Two hardenings as rules, not gates**: (i) `build_frame_anchor`
  never loses bits — the 64-bit array-type path, or a loud
  `Hike_diag` refusal of an absurd `n` (never a silent truncation);
  (ii) `frame_dims` degrades an absurd span to the bounded arm, not
  to a multi-exabyte request.

## Acceptance

- spill_many flips green at -O2 (the pin 7 → 6); `main`'s frame
  returns to ~240 bytes / anchor 232 (the merge-t1 shape).
- All gates green (strict -O0 37/37, opt-safety, referee 0,
  runtest == the 8 baseline); the golden list + AGENTS.md move in the
  merger's commit.
- Verdict: the rule, the case-count delta, the gate table, the pin
  movement, and the sweep note: any -O2 binary with a call after
  heavy 64-bit arithmetic was exposed to the same misfire — the
  convergence table re-checked for it.

Worktree: `/home/tovpr/hike-t14`, branch `tm/t14-escape-extent`.
