# 03: Fix vacopy/variadic frame/stack shape (va_arg_vacopy, variadic)

**What to build:** The remaining va_arg fixtures `two_pass` and `sum_n` achieve the same exclusive shape invariant as `consume_mixed`, closing the last two `check_allocas.sh` (d) failures and the three `llc` failures together.

**Blocked by:** 01: Fix hike_stack GEP helper (rebase_addr)

**Status:** ready-for-agent

- [ ] `bash scripts/check_allocas.sh` reports 124 passed, 0 failed (all three va_arg binaries PASS (d))
- [ ] `bash scripts/semantic/run_semantic_all.sh` no longer reports `(llc)` for `va_arg_mixed`, `va_arg_vacopy`, `variadic`
- [ ] No regression in `run_corpus.sh` diagnostics beyond the expected guarded poison
