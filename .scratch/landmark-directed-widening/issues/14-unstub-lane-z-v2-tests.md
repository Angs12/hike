# 14: Unstub Lane Z v2 landmark tests (test_cbat.ml)

**What to build:** Replace the "Stub to keep build green" Lane Z v2 blocks in `test_cbat.ml` with real external-behavior assertions for the Simon & King extrapolation: `Clp.widen_join` Listing 4, loop-bound convergence, and fixpoint value. Tests should check behavior, not implementation details, so they don't churn with refactors.

**Blocked by:** T08 (Wire consumption at the widening point (cbat_vsa.ml)).

**Status:** ready-for-agent

- [ ] Lane Z v2 blocks assert real behavior (not stubs); `dune runtest` exercises the landmark extrapolation
- [ ] A loop-bound convergence test and a fixpoint-value test pass
