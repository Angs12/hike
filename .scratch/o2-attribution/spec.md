# o2-attribution — the -O2 corpus semantic program's first lane

Settled 2026-09-09 (grilling session; decisions are the owner's).

## The program

- **Goal: the -O2-corpus semantic gate reaches 32/32.** Committed, not
  opportunistic: fix lanes are dedicated and ordered by evidence.
- **Enforcement is mechanical**: `run_semantic.sh`'s 4th argument
  (pinned-knowns mode) + `scripts/semantic/o2_known_failures.txt`. Any
  failing-set change is red — growth = REGRESSION, shrink = IMPROVEMENT —
  and the golden list moves only in the commit that deliberately updates
  it (the re-baseline rule).
- **Schedule = per-lane accounting**: every lane touching the VSA/emission
  stack reports red-list movement in its verdict; a no-movement lane
  records why. No calendar.
- **Order: attribution FIRST** (this lane), then fix lanes in attribution's
  ranking. The va_arg pair (`va_arg_mixed`, `va_arg_vacopy`) is the
  presumptive first fix lane, pending attribution.

## Starting evidence (2026-09-09)

- The gate: **25 PASS / 7 FAIL**; the failing set is byte-stable across
  five runs on 2026-09-09 (01:01 SP-lane battery failed the same seven
  plus `deep_recursion`; it flipped green in the simplification program's
  lane 3, NEQ/cell-meet conversions).
- **No regression**: a fresh `run_corpus.sh` emission of `/tmp/corpus_o2`
  is byte-identical 32/32 vs the battery's `cand-o2` reference (installed
  bundle sha16 `d018a1ee694ed6de` = the recorded final).
- **The record gap (the dig)**: no per-binary -O2 root-cause analysis
  exists anywhere in the repo or its git history. The only -O2-level text
  ever written is the pre-purge SP-lane verdict's class label
  ("indirect calls, setjmp, va_arg" — internally loose: no setjmp binary
  is in the set; array_local/byte_copy/fizzbuzz_safe/union_overlap map to
  none of the three). See `verdict.md`@`87a3945` (rewritten by `d3bb3fc`).

## Provisional priors (NOT -O2 findings — confirm or kill each)

Sources are -O0-era, escape-falsification, and precision-lane records;
several live only in git history (purged 2026-09-09, `5c96bec^`).

| binary | prior | source |
|---|---|---|
| array_local | widening casualty on the dynamic-index load; the unsound-narrowing namesake (AGENTS.md principle 5) | escape-narrowing `cand12` §3.1; architecture review 2026-09-04 |
| byte_copy | escape class: ADR 0008's full-deletion falsification list | `docs/adr/0008` §"the full deletion lost 5 binaries" |
| fizzbuzz_safe | thin: -O0 loop-bound class (fixed at -O0 only); opt-gate flip via mem-fission (dead push stores alias under instcombine) | semantic-gate-fix spec; purged AGENTS.md ~1453 |
| fptr_table | thin: "expected indirect-call class"; opt-gate flip via mem-fission | purged AGENTS.md ~366, ~1453 |
| union_overlap | value-side TOP: loop-index slot cell widens RAX (union cast); llc i32→i64 phi cast class; SFLOAT-lane IR delta | value-side-tops `cand15` §1.1; one-frame-anchor-removal `issues/02` |
| va_arg_mixed | va_arg reg-save-area / model-ABI class; mixed frame+stack_r define shape | purged AGENTS.md ~1755; gate-green-context `issues/02` |
| va_arg_vacopy | va_list address is a register-var → per-region alloca mispick; caller/callee argument-area offsets disagree | one-frame-anchor-removal README T03 + `issues/03` |

## Lane rules

- AGENTS.md principles hold as ever: NO GATES, NO FALLBACKS, soundness
  over precision; the semantic harness is the oracle.
- The golden list moves ONLY in the commit that flips a binary (fix
  lanes), never as a rider on an unrelated change.
- The pin's output IS the accounting: REGRESSION = stop; IMPROVEMENT =
  golden-file + AGENTS.md update land in the same commit as the fix.
