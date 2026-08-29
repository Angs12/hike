# 04: VSA lattice subsumes the relevance pass (wide refactor — expand–contract)

**What to build:** The relevance pass (`src/hike_vsa_relevance.ml`) and
the VSA's `denote_def` filter are now a single analysis: the AI state
carries `sp_derived_vars` as part of its lattice, and the VSA's
transfer function updates both the abstract state AND the sp-derived
set in one pass. The relevance pass's `forward_vars` and
`backward_slice` fixpoints are GONE; the VSA's value-tracking IS the
relevance analysis. `hike_vsa_relevance.ml` shrinks to ~100 LOC:
just the tag-application post-pass (sets `relevant`, `stack_access`,
`dynamic_alloc` on each def based on the VSA's results) and the
100% VSA Tagging Invariant assertion.

This is a **wide refactor**: the AI state type changes (one new
field), `denote_def`'s signature widens, and the relevance pass's
API contracts change. Expand–contract:

1. **Expand**: add the new `sp_derived_vars` field to the AI state;
   the VSA's transfer function updates it; the relevance pass still
   runs alongside (uses the new field where it's available, falls
   back to its own analysis otherwise).
2. **Migrate**: route the relevance pass's callsites to use the
   VSA's output; verify each callsite's gates.
3. **Contract**: delete the relevance pass's old analyses
   (`forward_vars`, `backward_slice`); the relevance pass becomes a
   thin tag-application post-pass.

**Blocked by:** T02, T03. The relevance pass's tag-application
post-pass needs the VSA's output to include the per-def
classification (which T02 enables) and the `callee_arg_area_size`
(which T03 adds). T04 is meaningless without those.

**Status:** ready-for-agent (after T02 + T03 land).

- [ ] Expand phase: `Cbat_ai_representation.ai_state` adds
  `sp_derived_vars : Var.Set.t`; `cbat_vsa.denote_def` updates it
  (a def is sp-derived if its rhs contains a frame-derived register
  OR it produces a var that was already sp-derived); the relevance
  pass still runs and produces the same tags as before (no
  semantic change).
- [ ] Migrate phase: `hike_vsa_relevance.analyze` becomes a
  tag-application post-pass: for each def, consult the VSA's
  per-def classification (and the `sp_derived_vars` set) to set
  `relevant`, `stack_access`, `dynamic_alloc` tags. No separate
  forward/backward fixpoint.
- [ ] Contract phase: `forward_vars` and `backward_slice` deleted
  from `hike_vsa_relevance.ml`. The whole file shrinks from ~290
  LOC to ~100 LOC.
- [ ] `dune runtest` green; no regressions.
- [ ] `run_corpus.sh` 31/31 rc=0.
- [ ] `check_allocas.sh` 124/0.
- [ ] `run_semantic_all.sh` — no regression; ideally progress on the
  3 remaining failures (the VSA's value-tracking now reaches
  more defs).
- [ ] `AGENTS.md` §Current validation state updated.

**Notes:** The 100% VSA Tagging Invariant assertion stays in
`hike_vsa.ml` (it's an emitter-level invariant, not a relevance
invariant). The `dynamic_alloc` detection (the syntactic
`RSP := RSP - size` pattern match) stays in
`hike_vsa_relevance.ml`'s tag-application pass. The `Weak`
lattice value for untagged words is OPTIONAL for this ticket
(the relevance pass's old worklist still serves as a soundness
filter; the Weak lattice becomes a future performance optimization).
