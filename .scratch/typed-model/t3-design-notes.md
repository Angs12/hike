# T3 working design notes (the implementer's scratch — the verdict is the record)

## The measured hole in the flat-seed design (why the domain gains a symbolic base)

The mission says: seed RSP's word with the flat segment
`[2^62, 2^62+8MiB]` (step 1), NO new domain constructor. Measured against
the rules, that design cannot meet the acceptance bar:

1. **Tag precision**: the tag = denotation − 2^62 is 8MiB wide for EVERY
   SP-derived address (`RBP−8` ⇒ Range(−8, 8MiB−8)). Non-singleton tags
   kill regions/slots/STL wholesale; cell keys (mem lane) become 8MiB
   hulls that fuse every cell ⇒ weak updates everywhere ⇒ the backward
   lane's memory refinement (the L-pins' subject) collapses to top.
2. **Own/caller classification**: with an 8MiB smear every own-frame
   access is mixed-sign (lo<0<hi). D1's two lanes need a producer
   classification; no denotation-based test separates own from caller.
3. **No sound total rule for the mixed class**: frame-GEP reads %frame at
   anchor+8k — wrong data for caller-window truths (the args were never
   copied there ⇒ -O0 strict gate red on every stack-arg binary);
   hike_stack-base writes below the caller's SP — aliases under
   recursion (deep_recursion red); the runtime select is T7-dissolved
   and banned.

Root cause: a flat set loses the CORRELATION between the entry-RSP base
and every SP-derived address (hull subtraction doubles the width). The
settled design record (.scratch/stack-base-symbolic/spec.md stage 1)
already designs the answer: a stack-offset universe — the base is a
symbolic constant, offsets track exactly. DEVIATION RECORDED (mission
sanctions: "if the ticket/decisions are wrong on a point of soundness,
follow the acceptance bar and record the deviation").

## The design

Domain (`Cbat_clp_set_composite`): `StackOff of Clp.t` — value =
`stack_base_symbol + offs` where the symbol ranges over the segment
[2^62, 2^62+8MiB] (a MODEL constant, never widened).

- add/sub with a plain (base-free) operand: StackOff(offs ± plain) — exact.
- StackOff − StackOff: plain offs1 − offs2 — the base cancels: exact.
- StackOff ⊕ StackOff (add): plain concrete hulls (base appears twice).
- bitwise/compares-vs-plain/mul/shifts/extract/concat: degrade to the
  plain CONCRETE hull (the smear [2^62+offs_lo, 2^62+8MiB+offs_hi]):
  logand 0xF ⇒ [0,15] (fixed-bits, undecided — L1 structurally dead);
  comparisons vs small constants decide consistently with real pointers
  (2^62 is non-canonical: disjoint from every real user/kernel address).
- meet/join/widen/extrapolate between StackOffs: pairwise on offs —
  RSP loop drift lives in offs exactly as it did in the old offset lane.
- equal/precedes/cardinality/overlap (StackOff pair): offset space.
- min/max/elem/iter (concrete queries): the smear.
- splits_by + Mem.Key: OFFSET space (the per-sub cell-key universe).
- classify/bounds_of for tags: OFFSET space (via `relativize`).

API: `stack_word : Clp.t -> t`, `as_stack : t -> Clp.t option`,
`in_stack_segment : t -> bool` (plain bounded hull inside [2^61, 2^63) —
the degraded/realignment lane's re-tagging arm; the segment is
non-canonical so no real address can collide), `stack_bounds`,
`relativize`.

VSA: init_sol seeds the DEFAULT entry's RSP word with
`stack_word {0}`. `is_stack_access addr st` = the denotation is StackOff
(bottom arm kept) or plain-in-segment — ONE predicate, visitor-merged,
replacing is_seed + mentions_frame_var + frame_neighborhood. Tags =
classify(relativize(denotation)) — same tags as today for well-behaved
code (the acceptance bar). After the overlap merge, Range/Infinite with
lo ≥ 0 split into the new `Caller` kind (the producer classification for
D1's hike_stack lane). Frame relation, value_env, rewrite_addr,
apply_frame_def, seed_frame, frame_add_rsp, mentions_frame_var: DELETED.
prove_nonneg's stack_anchor: structural (address denotation is StackOff).
call_abstraction_frame: keep boundary = the RSP's OFFSET hull max;
escape ranges = offset bounds. outgoing_arg_stores/sp_displacement:
offset space via relativize.

Emitter: `Range|Infinite` ⇒ the ONE uniform rule (create_exp →
create_addr_ptr licensed by tag presence — the lo<0 test dies);
`Caller` ⇒ `hike_stack + (word − anchor_i64)` as ONE form (no select);
no-hike_stack (main) ⇒ create_exp (real-address lane). Dies:
rebase_addr, create_static_mem_access (both arms), is_positive_kind,
the L2 mixed-span arm. VLA/Unbounded/Dead/untagged lanes unchanged;
the is_precise region fast-path unchanged.

## Pins

VSK-EMPTY: `AI.equal (st guard) entry` (no frame field). The L-pins:
bounds unchanged (counter values are plain; cell keys offs-space =
today's rewrite-space); anchored_entry seeds StackOff{0} so fixtures run
the production universe. E1 keeps its concrete {0x1000} entries (a
fixture may choose a known-RSP scenario; the mechanism under test — the
matched-pair +8 — is representation-independent).

## Stage plan

A. composite StackOff (+mli) — referee/property green.
B. VSA flip + memory lane + walk/transfer deletions + fixtures/pins.
C. emitter + kind plumbing (convutils, stack model, sigs).
D. battery, convergence, verdict, AGENTS.md.
