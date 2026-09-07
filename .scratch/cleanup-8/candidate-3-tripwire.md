# Candidate 3 (non-convergence tripwire) — exploration verdict: DO NOT BUILD

Source: 2026-09-04 architecture review, card 3 (Worth exploring):
oscillation tripwire behind the fixpoint interface (same sound degraded
verdict), with an open precision-first reframe (converge instead of trip).
Tree: cleanup-8 tip. Probe: `zz_scratch_probe/nc_autopsy.ml` (vsa-debug
only; catches the raise and dumps `Stages.stats()` + `memo_stats()`).

## The card's premise is gone

The motivating case — sort `sub_4d2a` burning 6000 visits for 798
blanket-Unbounded tags — **converges under the C8 worklist**: 3.47s,
609 real tags, measured 2026-09-06 (`subtimes /usr/bin/sort`). The "3.2s
burn" no longer exists. What remains is one boundary case below.

## What remains: cksum_avx2, and it is not what the card describes

| measurement | result |
|---|---|
| gate set (35 binaries, incl. sort/grep/gcc-12) | **0 non-convergences** (repeated) |
| full cu-perf census (102 loadable binaries) | **0 warns this round** |
| cksum_avx2 across runs at cap 6000 | **flaky**: trips some runs, converges others (479 real tags when lucky) |
| cost per trip | ~1.1–1.8s wall |
| cap 9000 / 12000 | trips 2/2, 3/3 |
| cap 60000 | **converges 5/5 in ~2.4s** |

Autopsy of a trip (counters at the raise — the probe's whole point):

```
TRIPPED after 6000 visits, 1.204s wall
STAGES-AT-TRIP denote 0.209s/6937 walk 0.045s/7 join 0.724s/12000
WALKS-AT-TRIP pops 1792 blocks 1799 truncs 7 max_pops 256
MEMO-AT-TRIP lookups 6944 hits 6 stale 5171 stores 6938
```

And of a success (cap 60000):

```
STAGES: denote 0.441s/14240 join 1.522s/24648 equal 0.030s/12326
        widen 0.001s/1 walk 0.099s/17 scaffold 2.022s/12324
```

Mechanism, read off these numbers: **slow legitimate ascent, not
oscillation.** It needs ~12.3k visits (hence 9000/12000 trip, 60000
converges); **widening fires exactly once** in the whole run; joins
dominate (1.5s of 2.4s, 24.6k joins); the backward refinement is nearly
silent (17 walks). Nothing cycles — values ascend monotonically through
2950 blocks (~2 visits/block average at trip) and the 6000 cap cuts the
ascent halfway. The run-to-run flakiness is consistent with hash-order
sensitivity in pop order (not diagnosed to root cause — one honest
unknown), and it is load-bearing for the verdict below.

Structural color: the sub is 2950 blocks / 3285 defs with exactly ONE
high-fanin block (250 predecessors; graphstats). A 250-way join inside
the propagation path is the shape that makes plain-join ascent slow.

## Why a tripwire is the wrong move (two decisive arguments)

1. **It cannot distinguish this from doom — and here it would fire on a
   converger.** Any visit-count or no-progress heuristic trips on
   cksum_avx2 (steady ascent on every visit; the queue never drains
   because values keep legitimately changing). Tripping converts lucky
   479-real-tag convergences into permanent degradation. False positives
   are priced in TAGS, not seconds — the exact opposite of the card's
   "same sound verdict" framing, which only holds if the trip never
   fires on a converger. It would, on the only candidate we have.
2. **There is nothing to save.** ~1 sub per 102 binaries × ~1.1s ≈ 0.1%
   of corpus wall. The card's 35%-of-producer prize died with sub_4d2a.

## Recommendations, ordered

1. **Record the premise change** (this note): the burn class closed as a
   C8 side effect; the card is answered by convergence, not by tripping.
2. **Populate the gap payload** (small, safe, useful regardless):
   `Fixpoint_not_converged`'s third field (`(tid * tid) option`) is
   ALWAYS `None` — conv_diag can never report more than "no gap pair".
   At trip, report the top heads by visit count from the ALREADY-EXISTING
   `head_visits` table (nearly free, no new machinery). This is the
   enduring diagnostic value, and it is what a future non-converger
   investigation will actually need.
3. **Raise the cap instead of tripping (the precision-first reframe, made
   concrete): 6000 → ~15000.** Costs nothing on converged subs (they
   never touch it); converts boundary subs deterministically (observed
   need ~12.3k; 5/5 converges at 60000). Caveat, stated plainly: this
   also raises the ceiling on truly-hopeless inputs — but ZERO known
   hopeless subs exist post-C8 (both historical burners converge given
   budget), while one known boundary converger exists. Gate on the
   battery + re-measure; the 15000 number carries the hash-order-variance
   unknown above, so keep margin, don't tune tight.
4. **Cross-link, not scope:** the burn is join-bound (24.6k joins) — card
   2 (need-restricted joins) attacks exactly this sub's cost AND
   shortens its path to convergence. No action here.

## Method notes (reproducibility)

- Temp cap experiments (`max_steps` 9000/12000/60000) were done with an
  explicitly-marked one-line edit, REVERTED afterwards; `git diff -- src/`
  is empty and both profiles rebuild green. Nothing shipped.
- `nc_autopsy` stays as committed scaffolding (vsa-debug-gated,
  invisible to production builds) for the next non-converger.
- Corpus note: cu-perf `grep` is absent from `/tmp/opencode/cu-perf/binaries`
  (a junk file named `[` sits in its place — shell accident during the
  coreutils build, unrelated); census denominator is 102 loadable binaries.
