# 10: Rewire dune unit test gate

**What to build:** The unit test gate `dune runtest` actually builds and runs the CBAT VSA test harness, so a vacuous green (no test exe) is no longer possible.

**Blocked by:** None (can start immediately).

**Status:** ready-for-agent

- [ ] `test_cbat/dune` stanza restored so `dune build @runtest` produces a test executable from `test_cbat.ml`
- [ ] `dune runtest --force` prints `ALL CBAT TESTS PASSED` or a real failure, not `EXIT:0` with no exe found
- [ ] No regression in `dune build` for the main `hike` library
