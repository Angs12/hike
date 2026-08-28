# 05: Fix nested_calls multi-level threading (level1..5)

**What to build:** The five-deep `level1`→`level5` call chain threads `hike_stack` correctly at every level, so `nested_calls` computes the correct arithmetic result.

**Blocked by:** 04: Fix deep_recursion Caller Frame threading (recursive fib)

**Status:** ready-for-agent

- [ ] Lifted `nested_calls` stdout `nested result = 8141` byte-identical to native (was 221)
- [ ] No level in `out_nested_calls.ll` passes `inttoptr` of a non-`hike_stack` RSP as the `hike_stack` param
- [ ] `bash scripts/semantic/run_semantic_all.sh` no longer lists `nested_calls` as FAIL
