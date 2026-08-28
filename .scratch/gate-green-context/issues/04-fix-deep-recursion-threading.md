# 04: Fix deep_recursion Caller Frame threading (recursive fib)

**What to build:** The recursive `fib` sub correctly threads the caller frame via `hike_stack` pointer rather than materializing `inttoptr` of the caller's RSP, so the lifted `deep_recursion` no longer segfaults and is byte-identical to native.

**Blocked by:** 01: Fix hike_stack GEP helper (rebase_addr)

**Status:** ready-for-agent

- [ ] Lifted `deep_recursion` exits rc=0 and stdout `fib(10)=55` matches native (no segv rc139)
- [ ] No `call @fib` in `out_deep_recursion.ll` passes `inttoptr i64 %RSP` as `hike_stack`; the `hike_stack` arg is a `ptr` GEP-derived value
- [ ] `bash scripts/semantic/run_semantic_all.sh` no longer lists `deep_recursion` as FAIL
