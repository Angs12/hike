# 02 — Empty-seed/mixed-seed oracle fixture

**Status:** ready-for-agent
**Depends on:** none (pins behavior that holds on the current tree; run it against
the pre-01 tree first to prove it passes before versions change meaning)
**Blocks:** 03

**What to build:** the seam-level pins for refinement identity and refinement effect.

- [ ] One fixture through the library seam asserting identity (refined state equals
      input state) on the empty-seed shape — pins the existing early exit that
      already serves 9–33% of calls.
- [ ] Mixed-seed refined-value assertions in the same fixture style as the
      fallthrough-shape oracle (absolute value sets, no implementation peeking).
- [ ] Fixture green on the pre-01 tree (it pins existing behavior) and stays green
      under ticket 01. Strict jne-counter check untouched and green.

Gates:
- [ ] New fixture green pre- and post-01; unit suite 0 FAIL.
