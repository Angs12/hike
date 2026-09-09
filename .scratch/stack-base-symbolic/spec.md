# stack-base-symbolic — the single-channel provenance program

Settled 2026-09-10 (grilling). The owner's directive: merge seeding into
the visitor — one `is_stack_access` predicate via denotation (channel 2
on every address) — and DELETE the SP-derived tracking (the frame
relation).

## Why it needs a domain extension first

With concrete offset words (`RSP ⇒ Range(-24,-24)`), guard expressions
evaluate on fake offset bits and prune live edges — the L1 class,
measured. The sound single-channel design therefore seeds a **symbolic
stack base** (`stack_0`) in the word domain:

- `add`/`sub` constants propagate the symbol (`stack_0 + k`);
- bitwise ops / comparisons on symbolic words go TOP-unknown (sound —
  the L1 class becomes structurally impossible, `value_env` is deleted);
- `is_stack_access addr st` ≡ the denotation of `addr` is a
  stack-symbolic set; the tag = the offset set (the denotation minus the
  base);
- cross-check: a stack address compared against a concrete address is
  never equal — the disjoint-universe semantics adds precision for free.

The emitter is untouched: it consumes tags; tags for well-behaved code
are identical (same offsets).

## Stages

1. **Domain**: a stack-offset universe in `WordSet` (`StackOff`):
   arithmetic propagates; bitwise/compares escape to TOP-unknown;
   meet/join pairwise; `classify` reads the inner offsets. Property
   suite + referee gate it.
2. **Flip seeding**: `is_stack_access` = the denotation is a stack-offset
   set (visitor-merged, one predicate). The L3 words-lane def-use fixes
   merge here — the words lane becomes the sole provenance carrier.
3. **Delete**: the frame relation (`seed_frame`, `apply_frame_def`,
   `frame_add_fvar`, `mentions_frame_var`, `rewrite_addr`), `value_env`,
   and the two-channel split.

## Why the frame relation exists today (recorded before it dies)

`seed_frame` seeds RSP with the constant offset 0 and tracks every
SP-derived var's offset through `apply_frame_def` — the offset fiction
the memory lane keys cells by and `rewrite_addr` rewrites addresses
with. It replaced an earlier symbolic-anchor design (`set_stack_0`); the
reason is lost to the records purge (`a113a7b`). The words lane's
def-use fidelity (L3) is the precondition for returning to it.

## Stage 1+2 status (2026-09-10, WIP on the stack-base-symbolic branch of work)

- seed_frame's fconst = the bounded segment range [2^62, 2^62+8MiB];
  init_sol seeds RSP's word with it (default entry only — fixture
  entries keep their own words).
- value_env still present (deletion waits on the full flip validation).
- ORACLES GREEN with the flip: referee 2,861,148/0; -O0 semantics
  33/33; allocas 165/0.
- OPEN (the flip's tail): 7 unit pins fail because they encode the OLD
  cell-key universe (small offset words) — VSK-EMPTY, L-D6, L-D2,
  L3c5-3a/b, L3c4-4, L3c3-1. Each must be re-derived in the segment
  universe and updated WITH verification (the bounds may still hold,
  keyed differently) before this lands as more than WIP.
- The entanglement recorded: denote_def's rewrite_addr materializes
  offsets into the word lane; the seed and the rewrite/keying are one
  coordinated representation — stage 3 (deleting the frame relation)
  cannot precede the words-lane def-use fixes (L3).
