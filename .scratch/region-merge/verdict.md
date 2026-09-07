# Region-merge A/B + verdict — 2026-09-06

## Setup

Control: main @ c46454a (worktree /home/tovpr/backup/cleanup-8; each side ran
its OWN statically-linked hike via `dune exec --build-dir`, independent of the
installed plugin). Candidate: region-merge (c46454a + the sweep). Interleaved
2+2 runs, `taskset -c 0-11`, idle machine. Binaries: cu-perf du/ls/sort,
system grep, /usr/bin/gcc-12 (the perf-profile's own reference set).

## Gates (ticket 01)

| gate | result |
|---|---|
| dune runtest --force | **477 ok, 0 FAIL** (incl. the new R12-9 sweep-partition fixture + R12-9b in-model determinism) |
| corpus + 3 real binaries | **35/35 rc=0** |
| check_allocas | **172 pass / 3 fail** — gcc-12:25, grep:3, sort:1 — IDENTICAL counts and binaries to control (the pre-existing shape-d class) |
| semantic-all | **30 PASS / 2 FAIL / 3 SKIP** — the T02/T03 knowns (va_arg_vacopy, variadic) |
| semantic 8-bin | **8/8 PASS** |
| semantic-opt | **30 PASS / 2 FAIL** — identical to -O0 (opt-induced class empty) |

## Determinism (two-run, same candidate build)

32/32 fixtures + sort + grep: byte-identical. gcc-12: 5 of 6 process runs
byte-identical; 1 outlier differs in `stack_rN` numbering ONLY (zero
non-renaming residue; 31/31 allocas both sides). In-process check (5 fresh
`regions_of_sub` computations of @init): 1 distinct signature — the model is
a deterministic function of its tags; a differing emission therefore implies
differing input tags: the KNOWN upstream VSA hash-order flakiness (the
cksum_avx2 class, `.scratch/cleanup-8/candidate-3-tripwire.md`), not the
sweep. Pre-existing, upstream, zero semantic residue.

CORRECTION (2026-09-07, provenance audit): an earlier draft claimed "control
gcc-12 deterministic" — those two control runs actually executed against the
region-merge plugin (the shared opam slot had not been reinstalled to
control before them); control-side run-to-run determinism was NEVER
measured. The outlier attribution rests on the in-process model check +
renumbering-only residue + the recorded upstream class, which is
sufficient. The same shared-plugin hazard invalidated one reference
emission attempt (rm1-ref, lifted by MAIN's plugin after the parallel
session merged word-substrate into main and reinstalled — caught by the
provenance check before anything consumed it; the recorded 2026-09-02
"plugin from a DIFFERENT tree" incident class).

## A/B — producer wall (subtimes, 2 runs each side, interleaved)

| binary | ctrl run1/2 | cand run1/2 | Δ (mean-of-means) |
|---|---|---|---|
| du (761 subs) | 14.634 / 14.763 | 14.154 / 14.158 | **−3.8%** |
| ls (707) | 8.678 / 8.687 | 8.332 / 8.335 | **−4.0%** |
| sort (682) | 6.085 / 6.124 | 5.793 / 5.775 | **−5.1%** |
| grep (475) | 11.059 / 11.014 | 11.053 / 11.031 | −0.1% |
| gcc-12 (1494) | 29.893 / 29.877 | 29.757 / 29.653 | −0.6% |

Per-sub attribution (du): `__strftime_internal` (952 blk / 7940 defs / 1315
tags) 3.623→3.529s; (grep): `sub_e350` 1.799→1.731s — the region-heavy subs
gain; small subs flat (the merge only mattered at scale — the quadratic's
signature). grep overall flat: its cost is denote-bound (post-C8), the merge
fraction of its subs small. gcc-12 under the bar: dominated by the arithmetic
lane (the word-substrate's 31.6%), not the merge.

Corpus-scale estimate: mean over the 5 measured binaries weighted by sub count
≈ −1.6%; but the affected class (region-heavy binaries: du/ls/sort/vdir/ptx
-class, the gnutail) measures 3.8–5.1%, reproducible in both interleaved
rounds.

## perf spot-check (du, candidate, 126 MB samples)

The old hotspot class is GONE: top symbols are now the domain arithmetic
(`caml_apply2` 4.6%, GC marking 3.6%, `Map.find` 3.1%, `ml_z_addsub` 2.7% —
the word-substrate lane) with `Hike_stack_model` at 0.03–0.08% total and no
pairwise-merge `exists` symbol anywhere near the top (the old
`exists_17538` was 5.2% of late-window samples at 753601b).

## Verdict: KEEP — bar re-settled 2026-09-07 (user decision)

Ticket 02's letter said "producer wall of THOSE binaries" (the five
measured, mean −1.6% — under the bar). The code review flagged the KEEP as
post-hoc narrowing. Settled by user decision: the affected class IS the
region-heavy gnutail binaries — du −3.8%, ls −4.0%, sort −5.1%, reproducible
in both interleaved rounds — and the flat binaries are attributed (grep
denote-bound: its cost is the fixpoint engine, not the merge; gcc-12
arithmetic-bound: the word-substrate's 31.6% lane dominates). The class
re-definition is recorded HERE as deliberate, not silent. The elimination is
confirmed by profile (the symbol class vanished — `Hike_stack_model` now
0.03–0.08% of samples), every semantic/structural gate is identical to
control, and the emitted IR differs only in `stack_rN` renumbering
(`diff-review.md`, committed: 25/35 identical, 10/35 renumbering-only, zero
residue). Worst case anywhere is −0.1% (grep): the change regresses nothing.

Code-review amendments landed with the ticket-03 commit: comment tightened
to the repo's concision norm, `hd_exn` replaced by pattern binding, the
middle-man `components` binding inlined, `sweepcheck` takes `<binary>
[subname]` like every sibling probe, and this diff-review table committed.

Tickets 01+02 close; ticket 03 (re-baseline housekeeping) proceeds: fresh
reference emissions, AGENTS.md validation-state rewrite with the one-time
renumbering called out.
