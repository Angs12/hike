# 02 — fix `meet`: disjoint circular intervals must be bottom

Depends on: 01 (the honest gate shows it red).
Blocks: none (03 is independent — the same rule applies).

## What to build

`Cbat_clp.intersection` (src/cbat_vsa/cbat_clp.ml; `meet` is its
alias at :1071) returns a NON-EMPTY set on genuinely disjoint
circular intervals — the R2-1 loose-hull class (the diophantine
anchor is clamped to `min_elem p2`). Fix so that the property holds:

  `property meet R5: the step-1 interval meet equals the exact
   circular-interval reference (widths 8/16/32/64)`

in test_cbat/test_properties.ml turns green, with the ~388 VIOLATION
counterexamples gone. The reference implementation (`r5_ref_meet`)
already lives in the test — it is the oracle.

Soundness direction: the current behavior OVER-approximates (returns
the full domain where the true meet is empty) — the fix NARROWS.
An unsound narrowing (excluding a reachable value) is a bug
(principle 5); the fix must make the result a SUPERSET of the exact
intersection and a SUBSET of today's result, or the property fails.

## The bar

- `dune runtest`: the R5 check green; ZERO meet VIOLATION lines.
- Full battery: corpus 32/32, IR byte-identity vs control, tag
  stability (kind multisets byte-equal on the converged heavy subs —
  grep sub_e350/9f00/4d2a style spot-checks), semantic gates unchanged.
- If tags move: STOP and investigate (AGENTS.md's
  investigate-before-landing clause) before continuing.
