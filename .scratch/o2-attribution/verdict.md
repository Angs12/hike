# o2-attribution — verdict (ticket 01)

Date: 2026-09-09. Method: mainline gdb/IR forensics + 3 parallel agents;
every binary's mechanism is runtime-proven (gdb traces, IR patches through
the llc+harness pipeline, or arithmetic decomposition), not inferred.
Artifacts: `/tmp/emit_fresh_o2` (IR+errs), `/tmp/sem_pin_a` (built
binaries+stdouts), `/home/tovpr/simplify-battery/cand3` (-O0 green
reference), plus per-agent dirs (`/tmp/fzwork`, `/tmp/vvc_gdb`,
`/tmp/pin_a`, `/tmp/fzsim`).

**The red list is FOUR mechanisms, not seven bugs.**

## L1 — Emitter poison arms going live (2–3 binaries)

The emitter emits `poison`/`llvm.trap` on program arms it deems dead
(`src/bil2llvm_mem.ml:253`: `Some Dead -> Llvm.poison`; the alignment-guard
trap arm). That is unsound exactly when the arm is live — and at -O2 it
is live twice:

- **fizzbuzz_safe** — PROVEN END-TO-END. The -O2 vector loop's 16-byte
  spill-reload (`paddd (%rsp),%xmm0`) lifts to `%2189 = or i256 %2188,
  poison` (IR:8666): the VSA bottomed the address set of a live def
  (`classify`, `src/cbat_vsa/cbat_vsa.ml:404`) → Dead → poison → llc
  lowers to 0 → the lane-increment vector zeroes from iteration 2 →
  counts 17 instead of 9. Patching the poison to the faithful constant
  prints **"FizzBuzz: 9"**. Produces NO diagnostic — the
  misclassification is silent.
- **va_arg_mixed** — the alignment-guard trap (`(model_addr+96)&15`) on
  the XMM reg-save store fires → SIGILL (rc=132, gdb at the `ud2`). The
  guard evaluates the MODEL address's low bits; the real program
  guarantees alignment via ABI. Bypassing the trap yields a **byte-perfect
  first output line** (the whole reg-save va_arg path is correct) — then a
  secondary divergence (loop state never advances) that this lane must
  re-check after the poison fix lands.
- **array_local** carries the same `or i256, poison` signature (IR:3088,
  3287) alongside the L3 signature — likely partially flips here.

Fix: **defense first (S)** — `Dead` must degrade to the sound fallback
(a real model-frame access), never poison (design rule 3: bottom is the
unsound answer, top/identity the sound one); same audit for the
alignment-guard trap arm → emit the unaligned access. **Root cause (M)**:
why the fixpoint bottoms live addresses (repro:
`conv_diag.exe -- /tmp/corpus_o2/fizzbuzz_safe main`; note the
misclassification is diagnostic-silent — consider a warn).

## L2 — Missing hike_stack rebase in the dynamic-load arm (1 binary, S)

- **va_arg_vacopy** — pass 2's overflow-area read is a phi-fed load whose
  offset range spans zero; `mem_access`'s `lo<0` arm
  (`src/bil2llvm_mem.ml:250-251`) emits raw `inttoptr` with NO
  `rebase_addr`, so the read lands in the callee's alloca-OOB pad
  (startup garbage = `1`). The positive arms (lines 215-219, 230-238)
  rebase correctly — and the -O0 lift rebases every such site (green).
  gdb-confirmed (`mov (%rdx),%esi` at 0x409ed5, `$rdx` = OOB pad). All
  five reg-save args are right; only the spilled 6th read is wrong.
Fix: apply `rebase_addr` in the `lo<0` arm too (the select is sound for
both signs). **S** — a few lines; no re-baseline risk (green binaries'
sites never reach this arm). No current carries (variadic/va_arg_mixed
checked); the risk shape is any -O2 merge of caller-frame derefs into a
mixed-sign phi.

## L3 — SSE lane-promotion def-use infidelity (3 binaries, M)

The lift promotes model memory into i256 "lane" phis; at -O2 gcc's
vectorized stores/loads meet that promotion and the def-use resolution
breaks:

- **union_overlap** — exactly one cell wrong (u[2]): stored
  `0x46D6050403020100` = bytewise-add of STALE lane state (bits of 0.25
  left by i=0's path) + the iota constant, because the broadcast byte
  merged into an unread lane while the consuming `paddb` read the stale
  phi. gdb trace reproduces the wrong total bit-exactly. The
  `guarded:`/Unbounded emission diagnostic is a RED HERRING (that memset
  store is correct). Prior (value-side TOP via loop-index) KILLED as
  stated.
- **byte_copy** — src holds a lane-permuted chunk (2-byte pairs drawn
  from pattern[57,58]/[61,62]/[25,26]/[29,30], duplicated) and
  src[16..63] never written (gdb): the vectorized init loop under-stores
  (1 of 4 chunks) and the lane arithmetic consumed stale state. The
  callee's copy is faithful over wrong data. ADR 0008 escape-class prior
  KILLED.
- **array_local** — same under-store + lane signature (one wide store;
  garbage sums with whole arrays reading as unwritten), plus L1 poison
  sites.

Fix: a lane-consuming op must meet the lane defs written earlier in the
same iteration (the producer-subtraction discipline the conditional lane
already has), plus the vector-store advancement. **M** — targeted rule in
the extraction/lane-merge (`src/cbat_vsa/`) feeding bil2llvm's lane
emission; -O0 is immune (scalar stores).

## L4 — Data-section relocation rendering (1 binary, M)

- **fptr_table** — the lifted `@data.rel.ro` renders `R_X86_64_RELATIVE`
  entries as RAW ADDENDS (4576/4608 = original-binary vaddrs); two
  function-pointer slots load from it, and the indirect call jumps to
  those raw addresses → SIGILL (rc=132). The `ptrtoint(@fnN)` slots are
  fine. NOT an indirect-call-semantics issue (the "expected
  indirect-call class" prior is KILLED — the indirect call is just the
  trigger). Any -O2 binary loading relocated data pointers is exposed.
Fix: the lifter's data emission must translate relative-relocation
addends into lifted-world addresses (or route such loads through
relocation-aware symbols). **M**.

## Ranked fix-lane order (evidence-strength × size)

1. **L2** (S, va_arg_vacopy) — mechanism proven, smallest change.
2. **L1** (S defense + M root cause; fizzbuzz_safe proven end-to-end,
   va_arg_mixed primary, array_local partial) — the Dead→poison rule
   violates design principle 3 and is diagnostic-silent; highest
   soundness value per line.
3. **L3** (M; union_overlap + byte_copy + array_local) — biggest binary
   count, one targeted rule.
4. **L4** (M; fptr_table) — isolated, data-emission owner.

Per-lane accounting: each lane's verdict must report red-list movement;
the golden list moves only in the commit that flips a binary.

## Red-list accounting for THIS lane

Pin state unchanged: **25/7** — this lane flips nothing (attribution
only); the golden file's provisional class comments were corrected to
this verdict (set untouched, re-verified green after the edit).

## Census (all 32 -O2 emissions)

trap = `llvm.trap` sites; cpLoad = wide loads from @rodata/@data/;
wideSt = wide stores; guard = `guarded:` in err; rN = stack_rN allocas.
Every failure carries a class feature; the converse fails (sret_big: 6
traps + 6 wide stores, passes). The Unbounded/guard class does NOT carry
(union_overlap is the only `guarded:` in the corpus, and it's harmless).
The stack_rN region split fired in 15/32 and all pass — the split lane is
healthy.

| binary | trap | cpLoad | wideSt | guard | rN | sem |
|---|---|---|---|---|---|---|
| array_local | 7 | 5 | 1 | - | 0 | **FAIL** |
| byte_copy | 1 | 1 | 1 | - | 0 | **FAIL** |
| fizzbuzz_safe | 2 | 1 | 0 | - | 1 | **FAIL** |
| fptr_table | 2 | 0 | 0 | - | 4 | **FAIL** |
| union_overlap | 0 | 0 | 0 | yes | 0 | **FAIL** |
| va_arg_mixed | 1 | 0 | 1 | - | 0 | **FAIL** |
| va_arg_vacopy | 8 | 0 | 2 | - | 0 | **FAIL** |
| sret_big | 6 | 0 | 6 | - | 0 | pass |
| alloca_vla | 0 | 0 | 0 | - | 1 | pass |
| bitfield_struct | 0 | 0 | 0 | - | 1 | pass |
| deep_chain | 0 | 0 | 0 | - | 0 | pass |
| deep_recursion | 0 | 0 | 0 | - | 28 | pass |
| factorial | 0 | 0 | 0 | - | 1 | pass |
| fizzbuzz | 0 | 0 | 0 | - | 4 | pass |
| landmark_loop_1000 | 0 | 0 | 0 | - | 1 | pass |
| list | 0 | 0 | 0 | - | 1 | pass |
| many_args | 0 | 0 | 0 | - | 1 | pass |
| mixed_fp_int | 0 | 0 | 0 | - | 1 | pass |
| nested_calls | 0 | 0 | 0 | - | 1 | pass |
| nested_struct | 0 | 0 | 0 | - | 0 | pass |
| printf | 0 | 0 | 0 | - | 1 | pass |
| ptr_chain | 0 | 0 | 0 | - | 1 | pass |
| rec_struct | 0 | 0 | 0 | - | 0 | pass |
| rmw_oob | 0 | 0 | 0 | - | 0 | pass |
| setjmp_longjmp | 0 | 0 | 0 | - | 2 | pass |
| setjmp_loop | 0 | 0 | 0 | - | 0 | pass |
| spill_many | 0 | 0 | 0 | - | 0 | pass |
| struct | 0 | 0 | 0 | - | 0 | pass |
| struct_arr_dynidx | 0 | 0 | 0 | - | 0 | pass |
| struct_by_value | 0 | 0 | 0 | - | 1 | pass |
| tail_callish | 0 | 0 | 0 | - | 0 | pass |
| variadic | 0 | 0 | 0 | - | 0 | pass |
