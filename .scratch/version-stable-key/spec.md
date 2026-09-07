# Version-stable memo key (candidate 4)

**Status:** ready-for-agent
**Area:** edge-refinement memo effectiveness on the relevance-free tree
**Decided in:** grill sessions 2026-09-04 (reframe: the memo exists, the disease is
misses; measurement split churn-vs-never-recur; shaping picked over content-hash)

## Problem Statement

The edge-refinement cache exists and is correctly addressed, yet it never hits:
0 hits from 5280 lookups across the slow subs of both large reference binaries.
Every miss is version churn — the same (block, jump) pairs recur hundreds of times
(e.g. 540 of 626 pairs recur on the worst sub) but a version counter moved in
between, so each visit pays the full nested walk (up to the 256-step cap, where the
largest subs spend 100% of refinement visits). Refinement is ~68% of fixpoint time
on the worst sub. As a lifter consumer I pay the walk on every visit; as a
maintainer I have a cache whose invalidation fires on updates no reader can see.

## Solution

Make versions semantic: a block's version counter moves only when its solution
state actually changes (store-time comparison with a physical-equality fast path —
persistent states share structure, so no-change detection is nearly free). Then
"version unchanged" means "data unchanged", the existing cheap integer-compare
lookup becomes exact with no lookup-time cost, and entries survive unrelated churn.
No walk-extent change, no seed policy, no precision change. Success is wall-time
reduction with the full gate battery unchanged.

## User Stories

1. As a lifter consumer lifting coreutils-scale binaries, I want the refinement cost proportional to real state change, so that fixpoint revisits stop repaying settled blocks.
2. As a maintainer of the fixpoint module, I want one invalidation story, so that vertex and walk readers share versions that mean data equality.
3. As a contributor profiling refinement, I want the churn-vs-recurrence split measured, so that cache work is argued from numbers (done: 0/5280, all churn).
4. As the author of the walk-extent follow-up, I want a hitting memo underneath, so that extent experiments measure extent, not recomputation.
5. As a reviewer of the single-pass design, I want cost held by measurement rather than gates, so that no soundness-adjacent skip ever returns under a performance pretext.
6. As a test author, I want the existing empty-seed early exit pinned, so that the 9–33% free win it already provides cannot silently regress.
7. As a consumer of the emitted IR, I want byte-identical output, so that a pure-cost change never moves my downstream.
8. As the planner of the optimizability program, I want the single biggest fixpoint cost attacked first, so that later precision work is timed honestly.

## Implementation Decisions

- **Shaping: bump-only-on-change.** Store sites compare old versus new solution state and skip the version bump (and ideally the store) when equal, with a physical-equality check first. Lookup path untouched: cheap integer compares over the stamped read set.
- **Content-hash-at-lookup considered and rejected:** it leaves stores dumb but makes every lookup traverse potentially large states with no structural-sharing shortcut — cost sits where equality is most expensive.
- **Scope: versions, not keys.** The (block, jump) address plus read-set stamping is already the right scope; only what a bump means changes. No new stamp dimension, no new module, no new external seam.
- **Miss behavior unchanged:** a genuine miss runs the exact current walk (structure, step cap, threading). Worst case is today's cost plus one lookup.
- **Seed-skipping explicitly dead:** all-TOP seeds measure ≤2.5% anywhere; no skip arm is built in this change. The empty-seed early exit that already exists (9–33% of calls) is pinned by fixture, not extended.
- **Walk-extent reduction explicitly sequenced out:** step-cap/adaptive work is a follow-up gated on this change's oracle plus probe deltas, never inline.
- **ADRs untouched:** single-pass design and the no-gate doctrine both stand; this is internal cost mechanics.

## Testing Decisions

- **A good test crosses the seam callers use.** Cache behavior is internal; refinement correctness is caller-visible and pinned at the library seam.
- **Modules under test:** the fixpoint module's version discipline (store/bump paths) and refinement behavior through the library seam.
- **Oracle:** the strict jne-counter acceptance check, the F1-FT fallthrough fixture (walk-equals-vertex pin), plus one new fixture pinning the existing empty-seed early-exit identity and mixed-seed refined values through the library seam.
- **Prior art:** the F1-FT fixture style (absolute value-set assertions through the library seam); the corpus battery as the no-regression floor.
- **Proof of the win is wall time:** producer totals and slowest-sub splits on the two large reference binaries against the same-day pre-change control, plus the unchanged gate battery.

## Out of Scope

- Seed-skipping of any kind (measured ≤2.5% — no prize).
- Walk-extent/step-cap changes (sequenced follow-up).
- New profiling stages or memo hit-rate counters in production builds.
- Any new pass, gate, tag, or face on the library seam; any precision work.

## Further Notes

- Key measurement (inlined against /tmp loss; full record was at /tmp/opencode/cand4/measure.md): 8 converged slow subs, both binaries — Walk_memo 0 hits / 5280 lookups; 626 distinct pairs with 540 recurring on the worst sub, 0 recurring hits; post-first churn 1234/1860 (66%); seeds mixed-Var 67–91%, all-TOP ≤2.5%, Cell 0, Infeasible 0; pops never below 65, largest subs 100% at the 256 cap; empty early-exit already covers 9–33% of calls.
- The reverted whole-map produced-value memo (prior spec, +18% regression) is the cautionary tale for this change: per-visit fixed overhead must stay below the per-hit saving, and wall time is the only accepted proof.
