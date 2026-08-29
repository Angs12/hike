# 04 — Fixture test + full gate rerun

**Depends on:** 01, 02, 03
**Blocks:** none

Lock the contract for the returning reader (you in 1 month, Q3) with a fixture test and full gate rerun.

Tasks:
- Add `test_cbat/test_relevance.ml` with two BIL fixtures: (a) SP-derived `Load` + chain `v := RSP + k; w := v + c` proves `stack_access ⊆ relevant` and phi contribution, (b) `RBP := RSP` then `Load(RBP)` proves `RBP` alone does NOT seed, only `SP` does; also `RDI := 0` alone proves NOT `relevant` unless it flows into (a).
- Run `dune runtest` (expect 315 + new tests green), then full gates: `dune build @install && dune install && cd src && bapbuild -clean && make`, `bash scripts/run_corpus.sh /tmp/corpus /tmp/heritage_relevance`, `bash scripts/check_allocas.sh` 124/0, `bash scripts/semantic/run_semantic_all.sh` 31/31, `dune exec test_cbat/corpus_watch.exe` / `precision_probe.exe` spot checks.
- Re-export `CONTEXT.md` terms and update `AGENTS.md` timestamp/validation state; note baselines invalidated by clean-break uuid.

Gate: all gates green, fixture documents SP-only + two-tag contract for the 1-month reader.
