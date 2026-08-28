# 01: Fix sub-signature alphabetical-order emission (10 of 11 semantic-gate failures)

**What to build:** `compute_sub_sig` in `src/hike.ml` emits sub parameters in
**alphabetical** order (BAP's `Term.free_vars` returns Var.t list sorted by
name), but the call site `create_call_args` in `src/bil2llvm.ml` (line
~1081) iterates `get_args ctx call_tid` (the stored signature) and reads
each param's value in **that same order** — so the args land in the wrong
registers, in the wrong YMM slots, and (for the 7th+ arg) in the wrong
stack position. The C ABI expects SysV order: RDI, RSI, RDX, RCX, R8, R9
(then stack). Lift the body computation, not the alphabet.

**Blocked by:** None (can start immediately).

**Status:** ready-for-agent

**Affected binaries (10 of 11 semantic-gate failures, all one root cause):**

| Binary | Symptom | Class |
|---|---|---|
| `factorial` | `inc(24,0,0,0,0,0,1)` returns non-deterministic rc (0..224) instead of 25 | 7th-arg unpushed (stack slot never stored) |
| `many_args` | `sum12(i,..,i+11)` prints garbage sum | 12-arg binding scramble + 6 stack args unpushed |
| `mixed_fp_int` | `combine(8 ints + doubles)` total=82 instead of 120 | 8-arg + 4-XMM scramble |
| `ptr_chain` | `traverse(2 S*, rounds)` segfaults (SIGSEGV, rc=139) | struct ptrs land in wrong regs → wild deref |
| `rec_struct` | `build(prev, v, depth)` segfaults (rc=139) | recursive struct: ptr + seed scramble |
| `struct_by_value` | `modify_copy(64B struct)` reads zeroed fields | struct split across wrong regs/stack |
| `nested_struct` | `sum_fields(A)` checksum off by 39% | struct A in wrong regs |
| `va_arg_mixed` | `consume_mixed(6 args)` doubles read as 0.0, ints scrambled | va_list register save area wrong |
| `va_arg_vacopy` | `two_pass(6, 6 ints)` trailing args garbage (220155904) | 6-int + 1 stack arg scramble |
| `variadic` | `sum_n(5 ints)` sum off | 5-arg + va_list scramble |

**NOT affected by this bug (different root cause):**
- `bitfield_struct` → see issue 02 (bitfield sign-extension in BAP-emitted bitfield ops)

## Symptom fingerprint

`compute_sub_sig` returns args in alphabetical order. Example from
`out_factorial.ll`:

```
@inc(i64 %R8, i64 %R9, i64 %RCX, i64 %RDI, i64 %RDX, i64 %RSI, i64 %hike_stack)
```

The C source is `inc(x, y, z, w, i, j, s)` (7 ints, SysV: RDI, RSI, RDX, RCX, R8, R9,
stack). The call site emits:

```
call @inc(i64 0, i64 0, i64 0, i64 %fact, i64 0, i64 0, i64 %sp_min_24)
```

— **alphabetical positional order**, so `0` lands in R8, `fact` lands in RDI,
`0` lands in RSI/RDX, the 7th arg `s=1` is passed via the `hike_stack` pointer
to the caller's frame. But the caller **never emits a `store` to that frame
slot**, so when `inc` does `inttoptr(hike_stack+8) → load i32` it reads
uninitialized stack memory — hence the non-deterministic rc.

## Acceptance criteria

- [ ] The arg list returned by `compute_sub_sig` for any sub matches the
      SysV ABI parameter order: integer regs in `(RDI, RSI, RDX, RCX, R8, R9)`
      order, YMM regs in `(YMM0, YMM1, ..., YMM7)` order, then `hike_stack`
      last
- [ ] The call site `create_call_args` reads the call's actual argument
      values in the same order (so a `call sub(RDI=a, RSI=b, ...)` is
      emitted as positional args matching the function's signature order)
- [ ] For any sub whose actual argument count exceeds 6 GPRs, the 7th+ arg
      is **stored** to the caller's frame slot before the call (so the
      callee's `inttoptr(hike_stack+8) → load` reads the correct value)
- [ ] `bash /tmp/opencode/regression_factorial_7th_arg.sh` reports
      `PASS` (currently 0/10)
- [ ] `bash /tmp/opencode/check_sem_failures.sh` reports 0 OUT_DIFF/RC_DIFF
      for the 10 affected binaries
- [ ] `dune runtest` remains all-PASS
- [ ] `bash scripts/run_corpus.sh` remains 31/31 rc=0
- [ ] `bash scripts/check_allocas.sh` remains 124/0
- [ ] No regression on the 8/8 `run_semantic.sh` gate
- [ ] AGENTS.md "CURRENT VALIDATION STATE" updated with the new numbers and
      timestamp

## Out of scope

- The `bitfield_struct` failure (separate root cause — see issue 02)
- Changing the SysV calling convention
- The 3 pre-existing unit-test FAILs (LM F1 + LM F2c × 2, see
  `.scratch/landmark-directed-widening/`)
- The 3 surviving `hike: guarded:` u128 warnings (by-design dead-branch
  poison per AGENTS.md design principles)

## Diagnostics (in `diag/`)

- `regression_factorial_7th_arg.sh` — tight, deterministic, ~3s regression
  test for the 7th-arg case (currently 0/10 PASS, expected 10/10 after fix)
- `check_sem_failures.sh` — runs all 11 failing binaries through the
  harness and reports per-binary failure class
- `last_run.txt` — captured output of the diagnostic loop on
  recover-golden tip (f83d01e)
