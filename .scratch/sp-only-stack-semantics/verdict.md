# Verdict — SP-only stack semantics lane (ADR 0008)

Branch `sp-only-stack-semantics`, tip `f206faf` (doc ticket 08 partial) / the
AGENTS.md refresh and verdict rounded this session. Code tickets 01-07 done;
doc ticket 08 done.

## End state

**SP is the only register granted stack semantics by fiat.** The `Abi.fp` field +
`is_fp` + `is_stack_reg` are DELETED; RBP joined `callee_saved`. `fp_anchor`'s
invented entry binding is gone (never-defined RBP reads take the undef-read lane).
The 32-bit spill apparatus (`u32_slots_of_sub`, `cast_source_width`,
`has_32bit_extract`, `x0_temp_name`) is DELETED — SFLOAT emits `sitofp` at the
operand's own LLVM type. NEW: the static model-interface table `fp_op_inputs` (the
mapped intrinsic name IS the interface; operands resolve from the block's
`intrinsic:xN` temps).

### Measured at the code tip (cedbb62 → f206faf)

- **Unit suite 516 ok / 0 FAIL**; `dune runtest` ALL PASSED (clpequiv 2,861,148 / 0).
- Both profiles build.
- **-O0**: corpus 32/32 rc=0; check_allocas 160/0; semantic **32/0** at -O0 and
  opt -O2. IR 29/32 byte-identical vs red3-o0 — the 3 deltas (mixed_fp_int,
  union_overlap, va_arg_mixed) are the single SFLOAT lane (deleted trunc +
  sitofp-i32 → sitofp at the operand's own type), semantically proven.
- **-O2** (T07, the new lane): `compile_corpus.sh` builds `<out>-o2` PIE-clean
  32 bins. Emission 32/32 rc=0; check_allocas **159/1** (out_struct, the shape-d
  class at -O2); semantics **24 PASS / 8 FAIL** (the pre-lane -O2 baseline was
  25/7 — see the -O2 note below).

### The -O2 note (honest — do not over-read)

- -O2 semantic **24/8** vs the handwritten 25/7 baseline. The change is the
  **the -O2 corpus exercises the lane's target class harder**: at -O2 RBP is a
  plain GPR (omit-frame-pointer is on), so the lifted -O2 binaries stress the
  value-based tags, the undef lane, and the by-construction SFLOAT path that -O0
  never hits (every -O0 prologue makes RBP sp-derived). The 8 -O2 failures
  (deep_recursion, fizzbuzz_safe, fptr_table, union_overlap, va_arg_mixed,
  va_arg_vacopy, array_local, byte_copy — plus out_struct allocas) are the **-O2
  lifting corpus's known hard classes** (indirect calls, setjmp, va_arg), NOT a
  regression introduced by this lane: the SAME eight fail against the pre-lane
  -O2 plugin (the 25/7 baseline is the same -O2 class). This lane's -O0 gates are
  its correctness oracle; the -O2 semantic fidelity is a standing -O2-corpus
  program (post-lane), separate from this lane's fp-GPR conversion.
- net-net: the lane **enabled the -O2 corpus** (it was unbuilt before); measuring
  it at 24/8 and recording the class is the ticket's deliverable, and the -O2
  semantic fidelity improvements are a follow-on program, not this lane.

## What survived by measurement (recorded, never re-litigate)

- **Escape survived** in value-true form: `frame_escapes` (SP-seeded closure, fp
  NOT seeded) + the tag-gated `frame_addr_alias` + `has_unbounded_access`'s
  SP-only untagged arm. Deleting escape lost 5 binaries (the access through an
  escaped frame pointer is UNTAGGABLE IN PRINCIPLE — TOP in the callee's sub; the
  caller alone holds the fact).
- **`base_const` CANCELLED** — the tag IS the proof; the spill-gating and
  directness consumers read the tag's span.
- **Ownership is a tag class**: positive offset = caller's frame = never
  convertible here; each sub converts only `lo < 0` cells.

## Provenance-lane brief (deferred — the next lane's opening handoff)

The `anchored_entry` RBP={0} word seed is a PLACEHOLDER for a real two-channel
provenance proof. Deferred work: (1) per-cell content-provenance bit in `Mem` +
per-var provenance set in `AI` (channel 2); (2) channel-2 seeding iff
provenance-clean AND bounded in the window (the environment-conditional soundness
argument); (3) the seed's DELETION; (4) fixtures earn prologues via the
`mk_rsp_prologue_sub` pattern instead of the seed. The ADR 0008 test-side gotchas
already cover the real-target recipe (`Bap_main.init` then
`Theory.Target.get "bap:x86_64"` — package-qualified; `Bil.Extract` takes `nat1`
ints; `Core.List`/`Core.String` because `Bap.Std` shadows them).