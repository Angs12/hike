# 03 — fix `logand`: elementwise-AND containment

Depends on: 01.
Blocks: none (independent of 02).

## What to build

The CLP and composite WordSet `logand` exclude reachable elementwise
ANDs (51 CLP + 33 Ws VIOLATION lines per run). Fix so the three
checks in test_cbat/test_properties.ml turn green:

  `property logand R10b: CLP logand contains every elementwise AND
   (widths 8/16/32/64)` / `composite WordSet` / `mixed-width coercion`

Soundness direction: the current result EXCLUDES reachable values —
the fix WIDENS (adds the missing witnesses). Widening is always sound;
verify the result stays a subset of top and the property's soundness
half holds on all sampled widths.

## The bar

Same battery as 02: runtest green on all three R10b checks, zero
VIOLATION lines, corpus 32/32, IR byte-identity, tag stability.
