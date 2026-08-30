# 01 — Wire inline edge-splitting + flip the consumer

**Status:** ready-for-agent
**Depends on:** none
**Blocks:** 02

**What to build:** the VSA's forward fixpoint becomes branch-sensitive end-to-end.
Every out-edge of every block transfers a **branch-refined** successor entry
state: the refinement is driven by BAP's **accumulated edge condition**
(`Graphs.Ir.Edge.cond` via `Sub.to_cfg` — probe-verified 2026-08-30: for
`when c1 goto l1; when c2 goto l2; goto l3`, the l2 edge carries `c2 & ~c1`
and the unconditional tail edge carries `~c1 & ~c2`), so a cond in a chain is
refined by every previous cond that was not true — the user's when-chain
directive, BAP-native. The offset-extraction consumer reads those refined
per-block entry states directly from the converged solution instead of from
the Phase B post-pass. Phase B code stays compiled but uncalled, so this
slice lands green without a simultaneous deletion.

The uniform edge transfer (from `docs/trace-partitioning-plan.md` §2/§4):

```
for each out-edge e of B (via Sub.to_cfg, precomputed once):
  Dst(e).in ⊔= deep_refine(B.out, Graphs.Ir.Edge.cond e g, sol)
# a lone goto's cond = 1 (identity); a chain tail carries ~c1 & ~c2 & ...
# raw B.out is NOT separately joined — every edge joins its refined state
```

Acceptance criteria:
- [ ] The transfer uses `Graphs.Ir.Edge.cond` (the ACCUMULATED condition),
      not the jmp's own cond — verified on a when-chain fixture: the mid-chain
      edge refined by `c2 & ~c1`, the tail edge by `~c1 & ~c2`.
- [ ] `edge_constraints` gains the two arms for `Edge.cond`'s syntactic forms:
      NOT-unwrap (`~(x op c)` → the complement row via `complement_guard_op`)
      and AND-conjoin (each conjunct seeds the same env).
- [ ] Every out-edge gets its refinement — conditional, unconditional, and
      chain-tail edges alike (the uniform rule); no edge is skipped.
- [ ] Call edges keep the existing frame-keeping call abstraction.
- [ ] The accumulated conds + the IR graph are precomputed ONCE per sub at
      fixpoint entry (static), never re-derived per iteration.
- [ ] `finish` (offset extraction) reads each block's **IN-state** from the
      converged solution; `partitioned_states` is no longer invoked.
- [ ] `edge_views_of`, `partitioned_states`, `edge_view` remain *defined and
      compile* but are uncalled.
- [ ] Landmark acquisition still fires (the walk's meets trigger `observe_unsat_var`;
      `widening_at_head` is bound around the block walk).
- [ ] The shallow jcc-decoder pre-step (`apply_operand_constraint` in
      `assume_jump_cond_with_group`) is KEPT — the deep walk is added on top, the
      shallow step is not removed (it carries the green F1-NEQ stabilization
      chain: guard-var meet + the `constrain_def_chain` MINUS-row walk; both
      paths share `constrain_def_chain` but deep-only equivalence is unverified).
- [ ] NEQ guards: DECODED `jne` refines the taken edge to the exact `TOP − {c}`
      (exclusion at the meet), `jz` pins taken to `{c}`; only NON-decoded NEQ
      guards fall back to taken-identity (the `comparison_constraint` `Bil.NEQ`
      `None` row).
- [ ] Gates green; emission parity with the current tree's own fresh emission
      (32 binaries — expected 32/32 rc=0, structural asserts 128/0, semantics
      29/3 + 8/8; the 3 known pre-existing semantic failures explicitly out
      of scope).

Gate: `dune runtest` all pass (incl. the strict F1-NEQ `max==K` staying green);
`run_corpus.sh` 32/32 rc=0; `check_allocas.sh` 128/0;
`semantic/run_semantic_all.sh` + `run_semantic.sh` parity.
