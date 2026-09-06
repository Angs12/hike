# Ticket 03 — re-baseline housekeeping and closure

Only after ticket 02 says KEEP.

1. **Fresh reference emissions**: the ticket-02 candidate emission
   (`/tmp/opencode/rm1-em` or a clean re-run) becomes the tree's IR reference
   (the re-armed byte-identity baseline). Record its path + the two-run
   determinism proof in the verdict.
2. **AGENTS.md**: rewrite CURRENT VALIDATION STATE with fresh numbers and a
   fresh timestamp; call out the one-time renumbering (region ids are now
   ascending-in-lo, tie-broken (lo, hi, tid); emissions pre-region-merge are
   NOT byte-comparable — use the new reference).
3. **spec.md**: append the closure note (verdict pointer, the collapse record
   stands).
4. **Commit discipline**: three commits (rewrite / A+B verdict / housekeeping),
   each green; `git merge` order into main is a fast-forward if main is
   unmoved.
