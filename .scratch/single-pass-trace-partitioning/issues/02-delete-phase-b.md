# 02 — Delete Phase B (dead code + rename + comment cleanup)

**Status:** ready-for-agent
**Depends on:** 01
**Blocks:** 03

**What to build:** with the consumer no longer depending on it, the entire Phase B
post-pass is removed — no dead code, no dead public surface, no stale references.
**This is bigger than dead-code deletion:** Phase B's API is load-bearing for the
test suite and the precision probe, so this ticket is also their migration.
Behavior is identical to 01; this is a pure simplification checkpoint.

Acceptance criteria:
- [ ] `edge_views_of`, `partitioned_states`, the `edge_view` record type, and the
      `_with_views` wrapper are deleted — from the implementation AND from
      `cbat_vsa.mli` (the deleted names are public API).
- [ ] The unit suite's view-based tests are MIGRATED to inline-refined IN-state
      assertions (the wrapper call-site fixtures, the view-lookup helpers, and
      the R6/G3 per-edge view assertions: taken = the `TOP−{c}` arc, fallthrough =
      `{c}` — note a multi-predecessor block's IN-state is the JOIN of its
      incoming refined edges, so per-edge assertions stay faithful only on
      single-predecessor destinations; the strict F1-NEQ check keeps passing).
- [ ] The precision probe migrates from the wrapper + `partitioned_states` to
      IN-state reads (the corpus watcher is already on the solution-only engine).
- [ ] `offsets_of_sub` drops the `views` binding; the production solve uses the
      solution-only engine entry point.
- [ ] Code comments citing the deleted machinery's `§`-numbers (`§1.2`, `§1.4`,
      `§2.2`, `§2.4`) are cleaned/updated.
- [ ] No remaining reference to any deleted name anywhere in the repo.
- [ ] Because the `cbat_vsa.mli` interface changes, the post-change corpus
      emission runs `cd src && bapbuild -clean && make` (the stale-interface
      gotcha — a plain `make` ships a stale cached interface).
- [ ] Gates green with no behavioral change vs 01: `dune runtest` all pass;
      `run_corpus.sh` 32/32 rc=0; `check_allocas.sh` 128/0;
      `semantic/run_semantic_all.sh` + `run_semantic.sh` parity (29/3 + 8/8,
      the 3 knowns out of scope).

Gate: same battery as 01, after a clean bapbuild rebuild.
