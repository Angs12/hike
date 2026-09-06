# Region merge — spec

Branch: `region-merge` (worktree `/home/tovpr/backup/region-merge`, off main @
c46454a). Grilling-settled 2026-09-06 (3 rounds, ~15 questions; rounds 1–2
under a byte-identity constraint that round 3's "semantics over bytes" answer
removed — the collapse is recorded below so nobody re-derives the lazy-adjacency
design).

## Problem

`Hike_stack_model.regions_of_sub` merges overlapping stack ranges into regions
via `merge_loop` (`hike_stack_model.ml:348-374`): a pairwise component scan
restarted after every merge event, `List.nth` access inside the discovery loops,
and `components_overlap`'s nested member-pair `List.exists` per candidate pair.
Measured cost: the stack_model phase is 4.8% of corpus wall and the inner
`exists` (`exists_17538`) alone is **5.2% of all late-window perf samples —
the single hottest hike symbol in the corpus** (103-binary coreutils profile,
176,957 samples, `.scratch/perf-profile/profile-2026-09-05-coreutils.md` §2/§6).

## Settled decisions

| decision | answer |
|---|---|
| landing base | fresh worktree off main @ c46454a (post-cleanup-8); decoupled from word-substrate T3–T5 |
| algorithm | **sort-and-sweep**: sort by `(lo, hi, tid)`, sweep with running max-`hi`, join when `lo ≤ max_hi` |
| equivalence claim | both algorithms compute exactly the connected components of the interval-overlap graph; the partition (which defs share a region) is identical. Sweep correctness: for every prior member `m` of the current component, `lo_m ≤ lo_j ≤ hi_j` holds by the sort, so `lo_j ≤ max_hi` iff `j` overlaps some member |
| what renumbers | only `stack_rN` names (`Convutils.id`); consumers verified order-agnostic — `region_by_tid` map lookups, commutative folds (span min/max, convertible for_all, max_width max), name-pattern matching (`stack_rN`/`_mem`/`_base` matched as a class, not by specific N) |
| determinism | tie-break `(lo, hi, tid)`; two-run byte-determinism re-arms the IR byte gate for future lanes |
| module shape | named private fn `merge_components` in `Hike_stack_model` — the overlap policy + determinism invariant get one home |
| gate | `dune runtest` green (mechanical fixture updates where ids are pinned) + full battery (id-agnostic) + renumbering-only diff review artifact + two-run determinism + **A/B ≥2% or revert** (interleaved `subtimes` producer on du/ls/grep/sort/gcc-12) + perf spot-check that `exists_17538` vanished |
| census | DROPPED — the A/B measures the win directly; the census sized a design (lazy rows/bbox) that no longer exists |
| fixture | dedicated partition fixture (designed overlap shape → expected components), replacing the sequence pin |
| commits | ① rewrite + fixtures, ② A/B + verdict, ③ re-baseline housekeeping |
| spec home | `.scratch/region-merge/` |

## The collapse (why not lazy rows / union-find)

Rounds 1–2 settled "lazy adjacency rows with an incremental frontier" under the
then-active constraint that the merge sequence (hence region ids, hence
`stack_rN` names in emitted IR) must be byte-preserved. Round 3's Q11 answer —
"it does not matter if they are byte identical, semantics are what we want" —
removed that constraint. The repo's prior record (AGENTS.md, the C3 verdict):
sort-and-sweep "renumbers regions corpus-wide and breaks IR byte-identity — a
deliberate re-baseline session, never a rider" — byte-identity was the ONLY
recorded blocker. With semantics as the bar, sort-and-sweep strictly dominates:
it eliminates the entire pairwise member-test class (not just the rescans), is
O(n log n) against the legacy O(n³)-shaped rescan, and is ~30 lines vs 3–4×
that for the row machinery. Union-find was never in play (same renumbering
issue, more code). The lazy-rows design is recorded here as the second-best
option if a future constraint ever re-imposes byte-identity of ids.

## Tickets

- `tickets/01-rewrite.md` — sort-and-sweep `merge_components` + the partition
  fixture; battery green
- `tickets/02-ab-verdict.md` — the A/B, determinism check, diff review, the
  ≥2%-or-revert verdict
- `tickets/03-rebaseline.md` — fresh control emissions (the re-armed baseline),
  AGENTS.md validation-state rewrite, closure

## Order and gating

01 → 02 → 03. One full battery at the end of 01 (the rewrite changes
emissions corpus-wide); A/B and determinism in 02 ride the same battery
artifacts; 03 is docs + reference emissions. The 2% bar (user directive):
if 02's A/B lands under 2% on the affected class, the lane reverts and records
the non-finding — the battery result does not keep the change by itself.
