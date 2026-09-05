# 02 — The F1-BUDGET fixtures

**Status:** blocked by 01
**Depends on:** 01 (the budget cell + enforcement must exist to construct)
**Blocks:** 03 (the fixtures must exist before the A/B pins them)

**READ FIRST:** the spec (`.scratch/c1-walk-budget/spec.md` §4 — the fixture
list is grilling-settled); the F1-NEQ / F1-FT fixture precedent in
`test_cbat/` (the T01 chain tests in `test_regression.ml` and the F1
properties in `test_properties.ml` show the construction pattern: a small BIL
sub built with `Test_common` helpers, driven through the real seams
(`Vsa.static_graph_vsa` with an `mk_rctx`-shaped context), asserting on the
solution's abstract states).

**Tasks:**

- [ ] **F1-B1 (soundness):** a small loop sub (the F1-NEQ counter-loop shape
      works); construct the context, set `!(rc_walk_budget) := 1` (tiny);
      run the fixpoint; assert: (a) the walk still returns a SOUND
      refinement — the guard-block's IN-state still satisfies the seed
      constraints it always satisfied (compare with `precedes`, not
      structural equality — the budget-limited result is a coarsening,
      never a narrowing); (b) the solution is NOT bottom anywhere a live
      block exists (no fake dead paths — principle #3).
- [ ] **F1-B2 (recharge):** a two-SCC sub (two sequential loops — e.g. the
      F1-FT fallthrough fixture's shape extended with a second loop); drain
      the first SCC's budget (set it tiny at the first recharge — or run
      enough walks to exhaust a small C); assert the second SCC's walks run
      with a FULL allowance (its refinement equals the unlimited result —
      the recharge proof: the second SCC is not starved).
- [ ] **F1-B3 (memo-first):** a sub where a walk memoizes under a full
      budget, then the budget is drained to 0; re-run the same edge; assert
      the memo HIT returns the cached refinement unchanged (the memo-first
      order refuses nothing free).
- [ ] Each fixture: `check` from the test harness, names in the
      `ALL CBAT TESTS PASSED` output (the suite is plain OCaml asserts —
      follow the file's existing style; if `test_seed.ml` is the seed
      collector's home, `test_properties.ml` or `test_vsa.ml` may fit
      better — pick by content, record the choice in the commit message).

**Verification:** `dune runtest` green with the three new checks listed in
the output.
