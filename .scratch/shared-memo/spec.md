# Shared denotation memo (merged candidates 5 + 11)

**Status:** closed 2026-09-04 — memo reverted, fixture kept (see Outcome below)
**Area:** fixpoint transfer cost on the relevance-free tree
**Decided in:** grill session 2026-09-04 (candidates 5 + 11 merged; per-def memo refined to
per-(block, version) whole-map memo on the user's version-granularity challenge)

## Outcome (2026-09-04)

Tickets 01–03 all implemented and merged to `shared-memo` (memo `16e8f4a`, fixture
`d3e3eed`), then the memo merge was REVERTED (`c0d7ffd`): same-day wall time showed
producer +18% on both reference binaries with zero subs improved (per-visit
whole-map build + lookup overhead beat the per-denote saving everywhere), precision
untouched, IR byte-identical. The F1-FT fixture stays as the oracle for any future
walk-extent work (post-revert: 450 ok / 0 FAIL). Seed-only extent reduction remains
the sequenced follow-up, ungated by this spec.

## Problem Statement

Since the relevance pass was deleted, the analysis denotes every definition, and the
fixpoint transfer got proportionally more expensive: per-denote cost is up ~61% at
identical visit counts, and one large binary regressed ~44% on producer wall time.
Profiling attributes the bulk to two denotation sites doing the same work — the
vertex transfer denotation on every visit, and the deep walk re-denoting every live
definition to obtain produced values for its meets. The walk's extent is not the
problem (every walk already truncates at its step cap with precision holding); the
repeated denotation is. As a lifter consumer, I wait longer for the same IR; as a
maintainer, I have two call sites computing one fact with no shared home.

## Solution

A single memo, keyed by (block, solution version), holding the whole
definition-to-produced-value map for that version. Whoever denotes first under a
version — the vertex transfer or the deep walk — populates the map; every later
reader under the same version reads instead of recomputing. The walk keeps its
sequential structure and its full extent (constraint propagation is order-dependent
and visit-specific); only the denotation calls drop out. No new pass, no gate, no
precision change when keyed correctly. Success is wall-time reduction on large
binaries with the full gate battery unchanged.

## User Stories

1. As a lifter consumer lifting coreutils-scale binaries, I want shorter producer wall time, so that large-binary lifts finish in minutes, not tens of minutes.
2. As a maintainer of the fixpoint module, I want one home for produced values, so that vertex and walk readers cannot diverge.
3. As a contributor profiling the transfer, I want wall-time proof of the win, so that I never debate memo effectiveness from first principles again.
4. As a future optimizer of the deep walk, I want the denotation cost already factored out, so that walk-extent experiments measure extent, not recomputation.
5. As a reviewer of the single-pass trace-partitioning design, I want the refinement's cost held by measurement, so that no soundness-adjacent gate ever returns under a performance pretext.
6. As the author of the edge-refinement follow-up, I want the full walk preserved, so that seed-only extent reduction can be trialed later against an unchanged baseline.
7. As a maintainer of the version discipline, I want the walk on the same versions as the vertex path, so that there is exactly one invalidation story to audit.
8. As a test author, I want a seam-level fixture pinning walk-equals-vertex values, so that a future memo keying bug fails loudly instead of drifting precision.
9. As a consumer of the emitted IR, I want byte-identical output for converged binaries, so that a pure-cost change never moves my downstream.
10. As the planner of the optimizability program, I want the transfer tax recovered before further precision work, so that precision experiments are timed against a true baseline.

## Implementation Decisions

- **One memo, whole-map granularity.** Keyed by (block, solution version); the value is the complete definition-to-produced-value map for that version. Per-definition entries were considered and rejected: versions are per-block, so every definition in a block invalidates together — finer addressing would add lookups with zero finer invalidation.
- **Single lookup per visit.** Each block-visit (vertex or walk) resolves its map once, then reads per definition as the retained sequential walk reaches it. No per-definition hit-testing.
- **Populate-on-miss from either path.** Vertex transfer and deep walk both store; duplicate stores agree because produced values are deterministic in (definition, versioned solution state). First visit after a version bump pays full cost (unavoidable cold miss).
- **Overwrite-on-bump eviction.** Exactly one map per block is retained; a version bump replaces, never accumulates. Stale entries cannot linger by construction.
- **The walk keeps its structure and extent.** Reverse iteration, producer-subtraction meets, operand-constraint derivation, and live-set threading are unchanged; the ~256-step cap is unchanged. A miss degrades to exactly today's behavior plus one lookup.
- **Existing version discipline reused.** No new stamp or epoch dimension. The version source is the per-block solution-version map both paths already share.
- **Version-bump audit rides along.** Every mutation path affecting a block's solution state (including flag states and call facts) must bump that block's version; a silent-mutation path is a soundness bug independent of this change, and the memo's block-at-once blast radius makes the audit load-bearing. The audit is a verification step, not a new mechanism.
- **Memo stores produced values only.** Constraints, live sets, and environment deltas are visit-specific and never enter the memo.
- **No new external seam.** The memo is an internal seam inside the fixpoint module; the library seam and the fixpoint's interface are unchanged. ADR-0003 (no pass, no gate) and the single-pass design both stand untouched.

## Testing Decisions

- **A good test crosses the seam callers use.** Unit fixtures inside the fixpoint module can pin the memo's hit behavior, but walk-equals-vertex equality is a caller-visible property and must be pinned at the library seam.
- **Modules under test:** the fixpoint module's transfer behavior (through the library seam) and the new internal memo (hit/miss/overwrite behavior).
- **Oracle:** the strict jne-counter acceptance check stays green, plus one new fallthrough-shape edge fixture through the library seam asserting refined pre-state values on the shared definitions (the shape whose lane proved load-bearing in the landmark-consumption fixes).
- **Prior art:** the existing strict acceptance fixture for guarded-counter stabilization; the existing corpus battery (emission identity, structural asserts, native-vs-lifted semantics at both optimization levels) as the no-regression floor.
- **Proof of the win is wall time**, not counters: producer totals and slowest-sub splits on the two large reference binaries, plus the unchanged gate battery. No new profiling instrumentation ships.

## Out of Scope

- Walk-extent reduction (seed-block-only refinement, adaptive early stops) — an explicitly sequenced follow-up, gated on the oracle plus probe deltas once this change lands.
- Any precision work: seeding policy, escape granularity, value-domain widening, per-call allocas. This change is precision-neutral by construction.
- New profiling stages or memo hit-rate counters in production builds.
- Any new pass, gate, tag, or face on the library seam.

## Further Notes

- Worst case is status quo: cold/stale misses cost exactly today's denotation plus one lookup, so a zero-hit-rate outcome regresses only by map-find overhead (to be confirmed by the wall-time proof).
- The chosen granularity came out of the grill: per-definition memoization was the opening proposal; the version-granularity challenge (versions are per-block, so all definitions invalidate together) promoted it to whole-map.
- Report home for the outcome: the architecture-review HTML (fold the merged candidate into the transfer-tax card) alongside the wall-time numbers.
