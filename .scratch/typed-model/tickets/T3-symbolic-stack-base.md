# T3 — the symbolic stack base + single-channel tagging (P1)

Spec: `.scratch/typed-model/spec.md` (binding constraints apply).
Design: `.scratch/stack-base-symbolic/spec.md` (the settled grilling
record — stages, the WIP status, the entanglement notes).
Blocked-by: **T1** (same emitter code region; the program's order).
Blocks: T4 (the tag/key universe it consumes), T7 is dissolved here.

## What lands

The full coordinated flip, ONE change, validated end-to-end:

1. **Domain**: a bounded stack-segment universe in the word domain —
   entry RSP's word seeded with the segment `[2^62, 2^62 + 8MiB]`;
   `add`/`sub` of constants propagates the symbol; bitwise ops and
   comparisons on segment words go TOP-unknown (the L1 class becomes
   structurally impossible — sound by construction, not by pruning);
   meet/join pairwise; classification reads the inner offsets.
2. **One predicate**: `is_stack_access addr st` ≡ the denotation of
   `addr` is a stack-symbolic set; the tag = the denotation minus the
   base. Visitor-merged, single channel; `vsa_info` stays the only
   carrier of stack-access-ness (the 100% Tagging Invariant).
3. **Delete**: the frame relation (`seed_frame`, `apply_frame_def`,
   `frame_add_fvar`, `mentions_frame_var`, `rewrite_addr`),
   `value_env`, the two-channel split.
4. **The uniform materialization rule** (spec §T3 — installs the
   general rule that subsumes the old per-tag address dispatch): every
   address word materializes as ONE step — `ptr = frame +
   (word − stack_0)` — total over all words, all signs, all widths. No
   positive/negative arms, no rebase selects, no span cases; the L2
   mixed-span special case dies with the dispatch.
5. **The 7-pin modernization**: the unit pins encoding the OLD
   small-offset cell-key universe (VSK-EMPTY, L-D6, L-D2, L3c5-3a/b,
   L3c4-4, L3c3-1) are re-derived in the segment universe WITH
   verification (bounds may still hold, keyed differently) and updated
   in the same change — never a blind expected-value rewrite.
6. **Segment-word consistency of the memory lane**: cell keys and the
   words lane consume the same representation (the WIP's entanglement
   note: the seed without relativized tags/keys broke the corpus
   22/33 — that failure mode is the acceptance bar's reason).

The failed WIP (reverted series 9f52c93..c10f699 on the program branch;
a `stack-base-symbolic` work branch may still hold stage-1+2 code) is
REFERENCE material: its oracles were green (referee 2,861,148/0, -O0
semantics 33/33, allocas 165/0) with the flip in place — reuse what is
sound, but land the whole coordination, not a seed.

## Battery protocol (you hold the shared plugin slot in your wave)

Same as T1's (see `.scratch/typed-model/tickets/T1-opt-safety-regression.md`
§Battery protocol): you are the wave's only `bap`/`dune install` user;
`record_provenance.sh` after every install; battery dirs on home disk.

Gates every iteration: `dune runtest` (referee + the modernized pins),
-O0 emission 33/33 rc=0, strict -O0 semantics 33/33, check_allocas
green, strict opt-safety 33/33 (T1's bar), -O2 emission rc=0, pinned
-O2 gate set unchanged unless a deliberate flip is proven.

## Acceptance

- All gates above green; the 7 pins re-derived and green in the
  segment universe.
- `value_env` and the frame relation are GONE (grep-clean); the
  per-tag address dispatch in the emitter is replaced by the one
  uniform rule; no new env vars, no gates.
- Verdict file: the gate table + the convergence report rows (the
  va_arg overflow residual — T7's subject — re-attributed here).

Worktree: `/home/tovpr/hike-t3`, branch `tm/t3-symbolic-base`.
