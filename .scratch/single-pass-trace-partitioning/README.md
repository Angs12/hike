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
ticket: `dune runtest` (all pass); `bash scripts/run_corpus.sh /tmp/corpus <out>`
(31/31 rc=0); `bash scripts/check_allocas.sh <out>` (124/0);
`bash scripts/semantic/run_semantic_all.sh` + `run_semantic.sh` (parity with
current emission; the 3 known pre-existing semantic failures are explicitly
out of scope).
