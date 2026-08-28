# 16: dune build + runtest green

**What to build:** The whole project builds and the unit-test gate runs the real harness green, integrating landmarks (T09) with the unstubbed landmark tests (T14) and the FP probe (T15). No vacuous green.

**Blocked by:** T09 (Remove the threshold ladder (no fallback)), T14 (Unstub Lane Z v2 landmark tests (test_cbat.ml)), T15 (FP regression probe).

**Status:** ready-for-agent

- [ ] `dune build` succeeds
- [ ] `dune runtest` runs `test_cbat.ml` and reports pass (no vacuous green / no test exe silently missing)
