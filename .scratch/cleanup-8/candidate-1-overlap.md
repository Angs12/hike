# Candidate-1 overlap census (2026-09-06, wshare probe — grill shelved, numbers kept)

Method: ifdef'd per-walk recorder in `refine_edge_inline` (guard-tid,
jmp-tid, seqno, Var/Cell seed counts, visited-block set) + `wshare`
probe (vsa-debug only): one producer run per sub, then per guard block
with ≥2 walked edges — mean/min/max pairwise Jaccard over cross-edge
walk pairs, union-savings ratio, seed mix. Scaffolding kept (committed);
`c1census` (one-off static jmp-count census used to name the second sub)
deleted after use.

## Results (both subs identical in structure)

sub_e350 (/usr/bin/grep): 313 multi-edge guards, 743 cross-pairs,
  union-savings **0.66**, seeds 100% Var / 0% Cell.
sub_8cb0 (/usr/bin/grep): 158 multi-edge guards, 406 cross-pairs,
  union-savings **0.66**, seeds 100% Var / 0% Cell.

- Jaccard **1.00 on every pair** (bestdiff=0 universally, incl. cross-visit
  pairs): same-guard edges visit literally identical block sets.
- Every walk set is exactly cap-sized (256/257 blocks): ALL walks truncate
  at the 256 cap, so cones coincide within the first-256-pops prefix;
  beyond-cap divergence is unobservable under the current cap regime.
- Static shape (c1census, since removed): e350 = 624 blocks, 356 with
  2 jmps; 8cb0 = 350 blocks, 174 with 2 jmps.

## Design implications (for a future unpack round)

1. The card's literal sketch (join seeds → walk → unpack) would refine
   NOTHING here: all observed multi-edge seeds are Var-only with
   differing per-edge constraints, which join to TOP. Any sharing design
   must carry per-edge constraints through the shared traversal (shared
   scheduling + shared denotations, per-edge live maps/meets/envs), with
   a Cell-seed fallback to per-edge walks (Cell seeds never observed on
   multi-edge blocks, but the fallback is required for generality).
2. Traversal is driven by live-var SETS (identical across edges of one
   guard — that is why the cones coincide); only constraint VALUES differ.
3. Prize bound under cap-256: ~0.66 × walk cost (~0.85s on e350-class subs
   IF per-pop flops are conserved; less if per-edge constraint flow costs).
4. Open from the dismissed round-4 grill: budget charging (charge-once vs
   per-edge), Walk_memo re-keying vs per-edge result memo. Undecided.
