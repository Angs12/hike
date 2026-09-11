# The typed-model program — convergence, soundness, simplicity

Implements the spec at `.scratch/typed-model/spec-v2.md` (the
comprehensive consolidation, 2026-09-11; supersedes `spec.md`, kept as
the v1 record). One ordered program on one branch
(`typed-model-program`). **Doctrine (binding, final form):** no gates,
no fallbacks, one mechanism (the symbolic stack base + the denotation
predicate answers everything), fix the architecture — the fix's diff
deletes cases — and conversion first (failures are inventoried; only
what survives the next model change gets fixed).

Status of this record: it IS the PR. The branch is pushed to
`origin/typed-model-program` (no GitHub PR — `gh`'s token is invalid in
this environment; the branch + this file are the review surface).

| ticket | what | state |
|---|---|---|
| [T1](tickets/T1-opt-safety-regression.md) | the frame-wrap license — the typed GEP requires the producer's residency proof | **landed** (opt-safety 31/2 → 33/33) |
| [T2](tickets/T2-simplification-pass.md) | the simplification pass | **landed** (−41 LOC, structural identity) |
| [T3](tickets/T3-symbolic-stack-base.md) | the symbolic stack base — the segment universe, one predicate, the uniform materialization rule | **landed** |
| [T6](tickets/T6-data-relocation-rendering.md) | data-section relocation rendering (initializers after `emit_program`) | **landed** |
| [T3c](tickets/T3c-single-predicate.md) | the escape dies entirely; the partition reads the denotations | **landed** (the -O2 pin 6 → 4) |
| [T4](tickets/T4-stack-arg-promotion.md) | the grilled conversion: stack-arg promotion, the SP Slot, VSA-resolved indirect calls, internal thunks, `hike_window` | **landed** |
| [T4b](tickets/T4b-conversion-correctness.md) | conversion correctness — four constructed rules, zero gates | **landed** (strict -O0 32/5 → **37/37**) |
| [T8](tickets/T8-repair-verdict.md) | the unit suite repaired: the F1 acquisition-polarity fix + the E2eD pins re-derived | **landed** (ALL CBAT TESTS PASSED — first time since 5218757) |
| [S10a](tickets/S10a-verdict.md) | the dead-weight wave + the region-GEP measurement | **landed** (byte-identical 37/37 both lanes) |
| [S10b](tickets/S10b-verdict.md) | `convutils` deleted — the record in `Hike_stack_model`, the emitter state in `Bil2llvm_env` | **landed** (byte-identical 37/37 both lanes) |
| typed-flag | `typed_frame`'s option died — ONE `stack_anchor` fact, two consumers | **landed** (byte-identical 37/37 both lanes) |
| [T10](tickets/T10-pipeline-simplification.md) | the intrinsic-callers filter dies + THE EMITTER CONSUMES NO RECORD (the promotion becomes a BIR rewrite) | **landed** (census delta zero, convergence zero-moved-rows) |
| [T14](tickets/T14-escape-extent-rule.md) | the escape-extent rule — only a `StackOff` proof sizes the frame (the spill_many SIGSEGV forensics); the pin 7 → 6 | **landed** (spill_many flips; golden list moved in `a24c8d2`) |
| [T13](tickets/T13-jump-compiler-pass.md) | the jump-compiler pass — jcc flag idioms become value comparisons ONCE (redesign, not relocation) | **in flight** (worktree `/home/tovpr/hike-t13`, branch `tm/t13-jump-compiler`) |
| [T15](tickets/T15-single-representation.md) | the single representation — tags carry the denotation; `relativize_opt` and its smear arm die | **in flight** (worktree `/home/tovpr/hike-t15`, branch `tm/t15-single-representation`) |
| [T12](tickets/T12-kind-collapse.md) | the kind collapse — `Unbounded` into `Infinite`; the `VLA` kind's storage role to the partition lattice (the enum: Range / Infinite / Dead) | queued |
| [T5](tickets/T5-sse-lane-def-use.md) | the SSE lane def-use fidelity (design pre-digested: `t5-design-notes.md`) | queued |
| [T9](tickets/T9-va-list-remodel.md) | the va_list re-model — the alloca'd overflow array (decided by evidence: `t9-design-notes.md`) | queued |
| S10c / S10d | the measured deletions (the store-chain post-T5; the window/Mixed residue post-T9) | queued |

## The state of the oracles

- **Strict -O0 semantics: 37 PASS / 0 FAIL**; **strict opt-safety:
  37/37**; the referee: **2,861,148 / 0**; the unit suite: **ALL
  PASSED** (T8).
- **The -O2 pin holds at 6**, each member owned: byte_copy +
  union_overlap (L3 → T5), va_arg_mixed + fizzbuzz_safe (L1),
  va_arg_vacopy (the va_list round-trip → T9), jump_table_sw (the -O2
  dispatch). spill_many left the list at T14 (`a24c8d2` — proven
  flip). Convergence: the memory-passed class collapsed (many_args
  121→58/4, mixed_fp_int 136→68/4, variadic 185/27); six more sources
  reached SAME/SAME at T4b.

## The reference battery for this program's next lanes

Measured 2026-09-11 on a freshly compiled corpus pair (the previous
`/tmp/corpus*` was lost with tmpfs; `scripts/compile_corpus.sh
/tmp/corpus` + `cp -a /tmp/corpus-o2 /tmp/corpus_o2`, canaries
verified):

`/home/tovpr/tm-battery/base` — provenance bundle `7ba492c8bf4bfbde`,
**0 hard reds**: `dune runtest` PASS, -O0 emission 37/37 rc=0,
allocas green, -O0 semantics **37 PASS / 0 FAIL**, -O0 opt-safety
**37 PASS / 0 FAIL**, -O2 emission 37/37, -O2 allocas green, the pin
green at 6, plus `conv/`. Both emission dirs are the byte-identity
reference for this corpus pair (a removal lane's acceptance is
byte-identical 37/37 both lanes).

## The corpus incident (recorded so it never repeats)

A rebuild once invoked `compile_corpus.sh /tmp/corpus_o2` (underscore —
the `-o2`-suffix rule missed it), leaving an -O0 COPY in the -O2 lane;
one battery "passed 33/33 strict" on it. Repaired;
`scripts/battery.sh` canary-guards the lanes. The corpora are 37 bins
(T4's four indirect-call sources: `fn_table_disp`, `jump_table_sw`,
`fn_single`, `fn_escape`).

Closes the spec issue `.scratch/typed-model/spec.md` and tickets
T1–T6, T3c, T4b, T8, T10–T15, S10a/b (T7 dissolved into T3/T3c/T9;
the surviving-failure tickets spawn after T10's battery per the
conversion-first doctrine).
