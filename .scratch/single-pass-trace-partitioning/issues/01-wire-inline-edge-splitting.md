# 01 — Wire inline edge-splitting + flip the consumer

**Status:** ready-for-agent
**Depends on:** none
**Blocks:** 02

**What to build:** the VSA's forward fixpoint becomes branch-sensitive end-to-end.
At every conditional GOTO the deep backward walk computes the two branch-refined
successor entry states and transfers each to its correct destination block; the
offset-extraction consumer reads those refined per-block entry states directly
from the converged solution instead of from the Phase B post-pass. Phase B code
stays compiled but uncalled, so this slice lands green without a simultaneous
deletion.

The edge-split transfer (from `docs/trace-partitioning-plan.md` §4):

```
t.in ⊔= refine_edge(edge P→t, True-cstr)    # taken, refined by c
f.in ⊔= refine_edge(edge P→f, False-cstr)   # fallthrough, refined by ¬c
# raw P.out is NOT separately joined — joining both would collapse to raw
```

Acceptance criteria:
- [ ] At every conditional GOTO (`Bil.If(c,t,f)`), the deep walk (`refine_edge`
      over both True/False `edge_constraints`) computes branch-refined IN-states;
      the raw block OUT-state is not separately joined on those edges.
- [ ] Unconditional `Jmp` / `Call` transfer is unchanged (identity join).
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
- [ ] Gates green (see README); emission parity with the current tree's own
      fresh emission (32 binaries — expected 32/32 rc=0, structural asserts
      128/0, semantics 29/3 + 8/8; the 3 known pre-existing semantic failures
      explicitly out of scope).

Gate: `dune runtest` all pass; `run_corpus.sh` 32/32 rc=0; `check_allocas.sh` 128/0;
`semantic/run_semantic_all.sh` + `run_semantic.sh` parity (incl. the strict
F1-NEQ `max==K` unit check staying green).
