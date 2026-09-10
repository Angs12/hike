# T12 — the kind collapse: Unbounded dies into Infinite (P2)

Owner directive (2026-09-11): "Why do we need both Unbounded and
Infinite? We do have directional infinites, and Unbounded should never
actually happen, and even if it does, should it not have the same
meaning as Infinite?"
Spec: `.scratch/typed-model/spec.md` (binding constraints apply).
Blocked-by: **T10** (it is rewriting `classify`'s extract and the
emitter dispatch this lane touches).
Blocks: nothing.

## The analysis (why the collapse is correct)

`Infinite` already carries DIRECTION — a widened interval with either
bound at ±∞ (the CLP lattice's directional infinities;
`WordSet.widen_join`/`extrapolate_steps` move them outward). `Unbounded`
means the address denotation is TOP — and in the same lattice TOP IS
the fully-infinite span `[-∞, +∞]`. Same meaning, same WordSet, same
emission (warn + plain materialization), same storage join (Frame).
The distinction is provenance only ("unknown" vs "widened") — a
distinction the pre-segment universe needed and the symbolic base
deleted. The kind is a leftover; the enum should be
**Range / Infinite / Dead / VLA** (+ the promotion's Caller/Mixed
vocabulary, post-T10).

## What lands

1. `classify` reads the denotation's bounds: a TOP-denoted address
   classifies as `Infinite` over the full span (the bounds ARE the
   answer — no separate kind, no special seeding arm; T4b's Unknown
   seeding becomes this rule).
2. The `Unbounded` constructor is deleted from the kind enum and from
   EVERY match (the emitter's mem_access arm merges into Infinite's;
   the storage lattice's Unbounded row dies — `Infinite[-∞,+∞]` joins
   to Frame exactly as Unbounded did, by the same lattice arithmetic);
   fixtures and pins updated with verification (the T8 precedent).
3. The diagnostic survives, re-keyed to the FACT: "unbounded span"
   fires when a Frame-joined access's bounds are the full domain (the
   T4b 27-line class keeps its warning — loud, as the doctrine wants).
4. CONTEXT.md: the Unbounded term merges into Infinite (directional
   bounds; the full span is the degenerate case).

## The re-measure

The kind merge may change partition/storage decisions where the two
kinds joined differently — expect emission deltas; the semantic gates
are the oracle. The -O2 pin: attribution-only movement recorded; the
 FAILURES INVENTORY carries anything unexplained (conversion-first).

## Battery protocol (you hold the shared plugin slot)

Same as T1's (see `T1-opt-safety-regression.md` §Battery protocol):
`eval $(opam env)` first; `record_provenance.sh` after every install;
battery artifacts on home disk (`/home/tovpr/tm-battery/t12/`). Gates:
`dune runtest` (the 8 baseline + named inventory; referee 0), emission
rc=0 both lanes, check_allocas green, strict -O0 semantics ALL PASS,
strict opt-safety ALL PASS or inventoried, the pinned gate
(attribution-only movement), convergence rows vs the pre-T12 reference.

## Acceptance

- Grep-clean: no `Unbounded` constructor anywhere (src, tests, probes).
- The enum: Range / Infinite / Dead / VLA (+ the promotion vocabulary).
- All gates green or inventoried; the diagnostic still fires on the
  full-span class.
- Verdict: the collapse mechanism, the emission deltas itemized, the
  gate table, the pin movement, the convergence rows.

Worktree: `/home/tovpr/hike-t12`, branch `tm/t12-kind-collapse`.
