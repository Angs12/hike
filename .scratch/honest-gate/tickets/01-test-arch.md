# 01 — the test-architecture commit (un-mute, delete, de-mechanize)

Depends on: none.
Blocks: 02 (meet fix), 03 (logand fix) — they land on the honest gate.

## What to build

One commit on `honest-gate`:

1. **Delete the mute mechanism** in `test_cbat/test_common.ml`
   (lines 33-72): the `ignored_substrings` list, `is_ignored`, and the
   `(stubbed)` print arm. `check` becomes: assert, count, print ok/FAIL.
2. **Un-mute the 22 passing checks** — automatic once the mechanism is
   gone; verify each appears as an honest `ok:` line.
3. **Delete check sites** (the check calls AND their fixtures):
   - `test_regression.ml`: regression C2, C3-outgoing ("does NOT
     survive as the stored concrete value"), C4a (the Infinite-tag
     one, NOT the passing "indexed loop-body store carries an offset
     tag"), C4b (the Infinite/Range one, NOT the passing control),
     property R11 (the un-hulled singleton, NOT the passing control),
     the ENTIRE R6 fixture, the ENTIRE G3 fixture, remediation A1
     (the TOP-valued escalation one, NOT the passing pre-call pin),
     A2, A3, A4c (the two "BOTH adjacent cells drop"/"neighbor cell
     OUTSIDE" — wait: the neighbor-cell-OUTSIDE one PASSES; delete only
     the red "BOTH adjacent outgoing-slot cells drop" one; the passing
     "pre-call neighbor cell" and "neighbor cell OUTSIDE ... survives"
     checks stay, muted→unmuted).
   - `test_vsa.ml`: T3-7b (dead), S-4b.
   - `test_properties.ml`: the 4 soundness checks (meet R5, logand
     R10b ×3) — UN-MUTED only (they stay red until tickets 02/03).
4. `dune runtest` output after this commit: exactly 4 FAIL lines
   (the soundness checks), everything else ok.
   **Amended 2026-09-07 (post-landing review):** the commit landed with
   3 FAIL, not 4 — the mixed-width logand R10b site was already green
   under the honest gate (its 8 sampled operand pairs did not trip the
   unsound mask arm); the red set was logand CLP, logand WordSet, and
   meet R5. The prediction was off by one; the end state after tickets
   02+03 is green either way.
5. Full battery: IR byte-identity 32/32 vs the pre-lane control
   (this commit must not touch production semantics — verify with the
   emission diff).

Careful: the substring list mutes by PREFIX — deleting a check whose
name shares a prefix with a KEEPING check requires renaming nothing;
just delete the right call sites. The final `check` count goes in the
commit message (the math: 543 baseline − deleted sites + nothing).
