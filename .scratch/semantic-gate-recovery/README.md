# Semantic gate recovery — triage overview

**Date:** 2026-08-28 14:35 EEST
**Tree:** recover-golden tip (f83d01e)
**Goal:** Close the 11 surviving semantic-gate failures
(`run_semantic_all.sh` 20/31 PASS) so the 31/31 PASS target is reached.

## Failure classification (11 binaries, 2 independent root causes)

| Class | Count | Binaries | Issue |
|---|---|---|---|
| **A: alphabetical sub-signature emission** | 10 | factorial, many_args, mixed_fp_int, ptr_chain, rec_struct, struct_by_value, nested_struct, va_arg_mixed, va_arg_vacopy, variadic | 01 |
| **B: bitfield sign-extension** | 1 | bitfield_struct | 02 |

## Triage order

1. **Issue 01 first** — fixing the sub-signature bug closes 10/11 failures in
   one diff. The fix is well-scoped (`compute_sub_sig` + `create_call_args`)
   and the regression test (`diag/regression_factorial_7th_arg.sh`) is
   tight, deterministic, and ~3s.
2. **Issue 02 second** — independent of issue 01, touches a different
   subsystem (bitfield ops, not signature emission). Small diff.

## Independent verification

- `diag/check_sem_failures.sh` — runs all 11 binaries through the harness
  and prints per-binary failure class
- `diag/regression_factorial_7th_arg.sh` — tight 3s regression test for
  the dominant bug
- `diag/last_run.txt` — captured output of `check_sem_failures.sh` on
  recover-golden tip (10/11 fail; the 11th — bitfield_struct — has a
  1-byte diff, also fail)

## What is NOT in scope (recorded in AGENTS.md as "Known regressions" or
"incident record")

- 3 unit-test FAILs (LM F1 + LM F2c × 2) — see
  `.scratch/landmark-directed-widening/`
- 3 surviving `hike: guarded:` u128 warnings — by-design dead-branch poison
- x87 lifter gap (coreutils dd/getlimits) — upstream BAP limitation
- X1-d absolute-immediate section addresses (coreutils gettext path) —
  PIE-only corpus, this class is structurally absent
