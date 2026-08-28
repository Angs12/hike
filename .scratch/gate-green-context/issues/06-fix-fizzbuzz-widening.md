# 06: Fix fizzbuzz loop widening / timeout

**What to build:** The counting loop in the fizzbuzz fixture converges within the bounded fixpoint chunks and the lifted binary terminates promptly with correct output.

**Blocked by:** 04: Fix deep_recursion Caller Frame threading (recursive fib)

**Status:** ready-for-agent

- [ ] Lifted `fizzbuzz` terminates within `timeout 15` (no longer rc124) and stdout byte-identical to native
- [ ] `bash scripts/semantic/run_semantic_all.sh` no longer lists `fizzbuzz` as timeout FAIL
- [ ] No new `Fixpoint_not_converged` warnings appear for `fizzbuzz` in `run_corpus.sh` stderr
