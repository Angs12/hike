# 02 — Delete Phase B (dead code + rename + comment cleanup)

**Status:** ready-for-agent
**Depends on:** 01
**Blocks:** 03

**What to build:** with the consumer no longer depending on it, the entire Phase B
post-pass is removed from the tree — no dead code, no dead public surface, and no
stale references in comments. Behavior is identical to 01; this is a pure
simplification checkpoint.

Acceptance criteria:
- [ ] `edge_views_of`, `partitioned_states`, and the `edge_view` record type are
      deleted.
- [ ] `static_graph_vsa_with_views` is renamed to `static_graph_vsa` and returns
      the solution only (no `views` component).
- [ ] `offsets_of_sub` drops the `views` binding.
- [ ] Code comments citing the deleted machinery's `§`-numbers (`§1.2`, `§1.4`,
      `§2.2`, `§2.4`) are cleaned/updated.
- [ ] No remaining reference to any deleted name anywhere in `src/`.
- [ ] Gates green with no behavioral change vs 01 (see README).

Gate: `dune runtest` all pass; `run_corpus.sh` 31/31 rc=0; `check_allocas.sh` 124/0;
`semantic/run_semantic_all.sh` + `run_semantic.sh` parity.
