# Hot-loop lanes merged: region-merge (card 1) + Transfer_memo deletion (card 4)

Branch: hotloops-merge (main @ 04c454f + e27a71b + 9fcb1ca). The merges
themselves were conflict-free; this file records the MERGED-TREE battery
(the lanes' own gates ran in their worktrees — see their own records).

## Merged-tree battery (2026-09-07)

| gate | result |
|---|---|
| dune runtest --force | 480 ok / 0 FAIL |
| corpus + sort/grep/gcc-12 | 35/35 rc=0 |
| IR vs the tm-del control emission | 26/35 identical, 9 renumbering-only, ZERO non-renaming residue |
| check_allocas | 172/3 = control's pre-existing shape-d |
| semantic-all | 32 PASS / 0 FAIL / 3 SKIP (both the hm-em and hm-em2 emission runs) |
| semantic-opt | 32/0/3 |
| semantic 8-bin | 8/8 |
| err/unmapped intrinsics | gcc-12's 26 = the pre-existing class, identical to control |
| two-run determinism | 26/35 identical; the 9 differing are renumbering-only, zero residue |

## The determinism finding (NEW, recorded for its own ticket)

The per-sub MODEL is deterministic — idstab probe (new, committed), 4/4
cross-process identical: regions, spans, ids, and the convertible plan
(main of landmark_loop_1000: r0(-32,-32) r1(-12,-12) r2(-8,-8) conv;
r3(0,0) r4(16412,16412) non-conv; plan [r0,r1,r2] every run).

The PIPELINE occasionally emits a different convertible set (run B named
the third alloca stack_r3 where run A named stack_r2 — a tag differed),
surfacing as pure renumbering. Root-cause class: the documented upstream
fixpoint hash-order flake (cksum_avx2, .scratch/cleanup-8/
candidate-3-tripwire.md: "run-to-run flakiness ... hash-order sensitivity
in pop order — not diagnosed to root cause; one honest unknown").
Region-merge EXPOSED the flake (renumbering makes tag wobble visible in
IR names); it did not create it — the same class predates the sweep
(the legacy merge order hid a 1-member plan change as a no-op). Both
wobble variants are semantically green (32/0/3 each, stdout
byte-identical).

**Open ticket (not a merge blocker):** diagnose the fixpoint's hash-order
instability. The idstab probe (cross-process region/plan signature) is
the instrument; the flake fires ~1-in-5 process runs on small fixtures.

## Main's own open perf item (flagged by the card-4 A/B, NOT this merge)

Producer wall on 04c454f measures +80% vs c46454a (du ~26s -> ~47s,
both A/B sides equally): the directional-infs/word-substrate merge.
Needs its own perf lane on main.
