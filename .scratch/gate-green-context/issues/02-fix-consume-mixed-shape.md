# 02: Fix consume_mixed frame/stack shape (va_arg_mixed)

**What to build:** The `consume_mixed` sub from the va_arg fixture emits an exclusive shape — either precise `stack_r`-only or degraded `frame`-only — not a mixed `frame + stack_r` define, satisfying the `check_allocas.sh` (d) invariant for this binary alone.

**Blocked by:** 01: Fix hike_stack GEP helper (rebase_addr)

**Status:** ready-for-agent

- [ ] `bash scripts/check_allocas.sh` no longer reports FAIL (d) for `out_va_arg_mixed`
- [ ] `out_va_arg_mixed.ll` contains no define with both `%frame = alloca` and `%stack_r` in same function when that function is the failing `consume_mixed` shape
- [ ] `bash scripts/run_corpus.sh` still 31/31 rc=0
