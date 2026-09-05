# 01 — The worklist driver + per-head warmup + global recharge

**Status:** ready-for-agent
**Depends on:** (none — the frontier ticket)
**Blocks:** 02, 03

**READ FIRST:** the spec (`.scratch/c8-worklist/spec.md`, ALL of it — the
design is grilling-settled; do not re-decide), ADR-0002
(`docs/adr/0002-single-pass-trace-partitioning.md` — the walk's inline
placement is NOT this ticket's concern), the C1 spec
(`.scratch/c1-walk-budget/spec.md` §2 — the budget enforcement you are
re-triggering, not redesigning).

**Tasks:**

- [ ] REPLACE `stabilize_comps`/`stabilize_scc` in `src/cbat_vsa/cbat_vsa.ml`
      with the succ-seeded WTO-priority worklist (spec §2.1–2.3): WTO
      position index from the existing WTO list (built once); ordered set
      with dedup; seed = entry block's successors; pop lowest; run
      `process_vertex` COMPLETELY (no dequeue-side skip); on `true`
      enqueue all Tid-CFG successors; stop on empty queue or
      `total_processed > 6000` (keep the backstop + its
      `Fixpoint_not_converged` raise exactly as-is).
- [ ] Per-head warmup (spec §2.5): a head-tid→visit-count map in the driver;
      replace the `!total_processed > 10` conjunct in `process_vertex`'s
      head arm with the head's OWN count > 10 (K=10, the mirror — do not
      tune). Non-head path untouched. `total_processed` keeps counting
      (backstop + Stages attribution).
- [ ] Global recharge (spec §2.6): delete the per-SCC recharge in the old
      `stabilize_scc`; recharge ONCE at fixpoint start
      (`budget := budget_per_edge × whole-sub out-edges`, summing
      `rc_out_edges` over all blocks — reuse the existing map).
- [ ] Everything else in `process_vertex` UNTOUCHED (spec §2.7 — memo
      order, seed derivation, meet fold, widening ladder, budget cap +
      decrement + no-memo-on-limited, all counters).
- [ ] `dune build` + `dune runtest` green. EXPECT suite movement: if an
      exact-value fixture (F1-NEQ max==K, F1-FT, T01 chains) fails, DO NOT
      "fix" the fixture — report WHICH pins moved and HOW (direction +
      magnitude) as the headline of the completion report. That movement IS
      the measurement ticket 03 judges.

**Verification:** build green, suite result reported fixture-by-fixture
(even if red — red is data), plus a vsa-debug `stage_timer` smoke on grep
sub_e350: visits (scaffold count) DOWN vs the recorded 2,334, walk pops
bounded by the same bhits/psaved counters.
