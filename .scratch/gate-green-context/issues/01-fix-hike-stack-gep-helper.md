# 01: Fix hike_stack GEP helper (rebase_addr)

**What to build:** The va_arg address lowering that currently emits `add ptr %hike_stack, i64 N` (which `llc` rejects as `expected value token`) emits a proper LLVM GEP instead, so any `hike_stack`-derived address compiles.

**Blocked by:** None (can start immediately).

**Status:** ready-for-agent

- [ ] No emitted `.ll` contains `add ptr %hike_stack, i64`
- [ ] `llc -O0 -filetype=obj` succeeds on `out_va_arg_mixed.ll`, `out_va_arg_vacopy.ll`, `out_variadic.ll`
- [ ] Verifiable via `bash scripts/run_corpus.sh` still 31/31 rc=0 with no new diagnostics
