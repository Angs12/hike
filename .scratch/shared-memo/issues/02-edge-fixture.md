# 02 — Fallthrough edge fixture (walk-equals-vertex oracle)

**Status:** ready-for-agent
**Depends on:** none (asserts behavior that holds on the current tree; run it against
the pre-01 tree first to prove it passes before the memo lands)
**Blocks:** 03

**What to build:** the seam-level pin for the memo's correctness invariant: the deep
walk must observe exactly the values the vertex path computes.

- [ ] One new fixture through the library seam in the fallthrough shape (arrow-less
      record operand through guarded refinement — the lane the
      landmark-consumption fixes proved load-bearing), asserting refined pre-state
      values on the shared definitions.
- [ ] Fixture passes on the pre-memo tree (it pins existing behavior, not new
      behavior) and stays green under ticket 01's memo.
- [ ] The strict jne-counter acceptance check stays green throughout (no edits
      expected; any failure is a stop-and-report event).

Gates:
- [ ] New fixture green pre- and post-01; unit suite 0 FAIL.
