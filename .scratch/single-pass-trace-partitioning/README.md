# Single-pass trace-partitioning

Fuse the VSA's backward-refinement / trace-partitioning into the forward
fixpoint and delete Phase B. Decided in the grilling session of 2026-08-29.

## Sources of truth
- `docs/adr/0002-single-pass-trace-partitioning.md` — decision, considered options, consequences.
- `docs/trace-partitioning-plan.md` — full spec (§1–§10: vocabulary, architecture, edge-split transfer, widen/landmark interaction, soundness/termination, consumer, deleted code).

## Ticket chain (dependency order)
- **01** — wire inline edge-splitting + flip the consumer (keep Phase B defined but uncalled)
- **02** — delete Phase B (dead code + rename `static_graph_vsa_with_views` → `static_graph_vsa` + clean historical §-comments)
- **03** — *(optional, deferred)* change-driven cache to bound the deep-walk cost

All tickets carry the `ready-for-agent` triage label. Validation gates for every
ticket (fresh emission from the CURRENT tree — the tree has moved since the plan
was written: it now carries the landmark-consumption ② delta uncommitted):
`dune runtest` (all pass, incl. the strict F1-NEQ `max==K`); `bash
scripts/run_corpus.sh /tmp/corpus <out>` (**32/32 rc=0**); `bash
scripts/check_allocas.sh <out>` (**128/0**); `bash
scripts/semantic/run_semantic_all.sh` + `run_semantic.sh` (**29/3 + 8/8**
parity; the 3 known pre-existing semantic failures are explicitly out of
scope).

Plan status: **re-verified against the post-② tree on 2026-08-30** — the
spec (`docs/trace-partitioning-plan.md`) and these tickets were refreshed:
NEQ now refines exactly for decoded `jne`/`jz` guards, the shallow jcc
pre-step is KEPT (not subsumed) to preserve the green F1-NEQ chain, Phase B
deletion's blast radius covers the `.mli`, the unit suite's view-based tests
(R6/G3) and the precision probe, and the gate numbers are the 32-binary
corpus's.
