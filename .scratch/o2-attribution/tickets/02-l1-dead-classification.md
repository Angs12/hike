# 02 — the L1 lane: the Dead misclassification repaired at the producer

DONE 2026-09-09. Two producer fixes + one emitter contract + the
k-ranges removal (the owner's doctrine: `vsa_info` carries per-def
offset ranges — nothing else).

## Root causes found (the dig)

1. **`reachable_jumps` evaluated guards on the fake offset words.**
   `denote_def` materializes a frame-tracked var's word lane as its frame
   OFFSET (`RSP := RSP - 24` ⇒ word `Range(-24,-24)`) — the addressing
   fiction the memory lane keys cells by. Guards are VALUE context: the
   -O2 stack-realignment idiom (`test (RSP & 0xF)`) evaluated on the fake
   offset decided a live branch impossible → the edge was pruned → the
   whole program body downstream never entered the fixpoint → init-bottom
   states → `classify` → Dead → emitter poison. FIX:
   `Cbat_transfer.value_env` — guards evaluate with frame-tracked vars'
   words set TOP (a stack address's base is unknown at compile time).
2. **`Clp.logand`'s `| None -> bottom`** — circular operands have no
   min/max; the unrepresentable-image arm produced BOTTOM (a live path
   claimed empty). FIX: None → top (design principle 3). The property
   suite (`property logand`, 1551 pairs) stays green.
3. **`create_def` bound over-wide values** — a `-O2` lane def
   (`v64 := low:128[X]`) stored an i128 under a 64-bit var's key; the
   loop-head phi then failed llc (`%168 defined with type 'i128' but
   expected 'i64'`). FIX: the width contract enforced where the value is
   BORN — trunc (over-wide) / zext (narrow) to the lhs var's declared
   width. NO phi coercion (the owner's ruling: values correct at birth).
4. **k_ranges removed from the product** — the pushed-arg discriminator
   (`has_outgoing_stack_args`'s k ≥ 0) is computed once in the extraction
   (`outgoing_arg_stores`, where the per-def state lives) and consumed by
   the escape analysis as an internal set. `vsa_info` = offsets + facts.
   MEASURED: dropping the disjunct entirely broke va_arg_vacopy and
   variadic at -O0 (the oracle fired); the internal-fact form preserves
   the semantics exactly.

## Result

- **array_local FLIPPED GREEN** (-O2 25/7 → 26/6 pinned): its two
  Dead→poison sites reclassified to real ranges.
- **fizzbuzz_safe**: the L1 poison is GONE from its IR (only the benign
  insertvalue idiom remains); the residual is the L3 store-side (its
  lifted-ud2 path is now reachable through the still-broken L3 lane
  values) → SIGILL rc=132. Owned by L3.
- -O0: 32/32 semantics, allocas 160/0, referee 2,861,148/0, byte-identity
  **29/32** — three itemized deltas (va_arg_mixed, va_arg_vacopy,
  variadic: the value_env refinement change), each oracle-proven. THE
  NEW -O0 REFERENCE EMISSION IS `/tmp/emit_l1_o0`.
- One new -O0 diagnostic line (the Dead warn, va_arg_mixed's
  genuinely-dead misaligned arm — correct and now loud).
- Suite: the failure set equals the PRE-EXISTING baseline (8 checks —
  E2eD-7/8, LM F1-* — measured via `git stash` to fail on the pristine
  tip; NOT this lane's regression; documented for the owner). The POISON
  pin flipped deliberately: the Dead arm now WARNS.

## Pre-existing suite failures (not this lane)

`E2eD-7/8` (top-addr store) and the LM F1 landmark pins fail on the
pristine 7e7bd26 tree. The referee and both semantic oracles are green.
The owner should triage them as their own item.
