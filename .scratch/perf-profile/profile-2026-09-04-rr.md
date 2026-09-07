# Perf profile: hike VSA/producer on coreutils-scale binaries — restriction-removal tree

Date: 2026-09-04 (second session). Host: same 20-thread hybrid Intel, 15GB RAM.
perf 7.1.12. `kernel.perf_event_paranoid = -1` (verified at session start).
Commit `3cd0dbf` (integration branch `restriction-removal`: relevance pass DELETED,
VSA self-seeding; old candidates 1+2 withdrawn for exactly this reason).
Built in own worktree `/tmp/opencode/rr-perf` (`-b rr-perf` @ `3cd0dbf`);
`dune build`, `dune build @install && dune install` all rc=0 there.
Dune profiles: default (timing) and vsa-debug (`--build-dir _build-debug`, `Stages` only).

Production sources untouched (read-only): all timing via existing probes
(`zz_scratch_probe/{subtimes,stage_timer,conv_diag}.ml`, vsa-debug `stageprof`),
`perf report` leaf symbols (no chains — see §5), `perf stat`, and gdb sampling.
No `src/` or `src/cbat_vsa/` edits. Method replicates `profile-2026-09-04.md` §2–§5;
its numbers are NOT copied — every figure below is re-measured. Old-tree figures
are quoted only as "old → new" deltas, with the old value cited to the old file.

Repro note: `perf record --call-graph dwarf` DOES NOT UNWIND the new-tree binary
(§5). Phase attribution below comes from `stage_timer` decomposition (direct
timing, strictly better than sample attribution) and the `Stages` adapter;
the inclusive-refinement check comes from `Stages` walk counters + live gdb
stacks. Flat top-15 comes from `perf report --no-children` (leaf symbols work).

## 1. Binaries profiled

| binary | size | PIE | #subs (`subtimes`) | producer total (`offsets_of_sub` over all subs, 2 runs) |
|---|---|---|---|---|
| /usr/bin/sort | 129744 | yes | 452 | **8.801s / 9.911s** (`/tmp/opencode/rr-subtimes-sort{,2}.txt`) |
| /usr/bin/grep | 211344 | yes | 475 | **15.148s / 16.812s** (`/tmp/opencode/rr-subtimes-grep{,2}.txt`) |

Old → new: sort 13.716s → ~9s (−36%); grep 11.133s → ~16s (+44%).
Run-to-run variance is ±10% (two `subtimes` runs each); the deltas are well outside it.

End-to-end context: `bap /usr/bin/sort --pass=hike-convlir` = **13.446s wall**
(13.14s user, 0.31s sys; `/tmp/opencode/rr-bap-sort.log`), so the producer (~9s) is
still **~65–70% of a full lift** (old: 13.7/21.0 = 65%).
`bap /usr/bin/grep --pass=hike-convlir` = **30.849s wall**
(`/tmp/opencode/rr-bap-grep.log`); producer (~16s) ≈ **~50% of the lift**.
(Both rc=0; stderr carries 1227/1286 `hike:` diagnostic lines respectively —
mostly guarded/undef-read, not timed here.)

Prefilter effect (`has_mem_ops`, `src/hike_vsa.ml:18-24`): sort 144/452 subs and
grep 135/475 subs produce 0 tags at 0.000s each — ~30% of subs are free.

## 2. Coarse triage: slowest subs (from `subtimes`, slowest-last; ranges over 2 runs)

sort (`/tmp/opencode/rr-subtimes-sort.txt`, `/tmp/opencode/rr-subtimes-sort2.txt`):
```
3.087-3.487s  ~35%     655 blk    5217 defs   798 tags  sub_4d2a   <-- STILL NON-CONVERGED (6000 iters); tags now all Unbounded (§3)
0.882-0.994s  ~10%     265 blk    2106 defs   301 tags  sub_9f00   (old: 528 tags)
0.754-0.842s  ~8.5%    299 blk    1580 defs    73 tags  sub_9570   (old: 133 tags)
0.542-0.612s  ~6%      137 blk    1233 defs   173 tags  sub_b380
0.434s        ~5%      149 blk    1450 defs   130 tags  sub_bd10
```
grep: top is `sub_e350: 3.955-4.409s, ~26%, 624 blk, 4210 defs, 216 tags`
(old: 4.614s/41.4%/703 tags), then 8cb0 ~0.93-1.03s, 6b60 ~0.85-0.95s,
296a0 ~0.75-0.83s — flatter than sort, same shape as old.

Tag-count deltas (identical counting, `Map.length info.offsets`): 9f00 528→301,
9570 133→73, e350 703→216, 4d2a 0→798 (all `Unbounded` from the degraded arm,
`src/hike_vsa.ml:80-89`). FLAGGED FOR THE CORRECTNESS LANE, not timed further
here: converged subs emit ~40–70% fewer offset entries on the new tree.

## 3. Phase split per slow sub (`stage_timer`, 3 reps each)

`stage_timer` pass 1 = production `offsets_of_sub` (= seed-detect + fixpoint +
extract + regions + split_plan); pass 2 = seed-detect + standalone fixpoint
(`zz_scratch_probe/stage_timer.ml:27-56`). No `analyze` lane exists anymore.

| sub | producer (pass 1) | seed-detect | fixpoint (pass 2) | extract+model tail (by subtraction) |
|---|---|---|---|---|
| sort sub_4d2a | 3.16-4.15s | 0.002s | RAISES `Fixpoint_not_converged`, rc=2 (as old) | degraded arm (Unbounded tags) |
| grep sub_e350 | 4.35-4.71s | 0.002s | 4.10-4.41s (**94-95%**) | ~0.2-0.3s (~6%) |
| sort sub_9f00 | 0.945-1.072s | 0.001s | 0.851-0.960s (**89-90%**) | ~0.1s (~10%) |
| sort sub_9570 | 0.798-0.875s | 0.001s | 0.725-0.737s (**86-91%**) | ~0.07-0.14s (~8%) |

Old → new per sub: 4d2a 10.4s (7.5 analyze + 2.75 fixpoint) → ~3.2s (seed 0.002 +
~3.2 fixpoint-burn + degraded extract) — the 7.5s backward slice is GONE, the
~3s non-convergence burn remains. Converged subs: e350 4.574 (1.478 + 3.052) →
~4.6 (0.002 + ~4.4); 9f00 0.896 (0.257 + 0.641) → ~1.0; 9570 0.772 (0.193 +
0.547) → ~0.84. **Converged-sub fixpoints are +33–44% slower; the deleted
analyze lane (−0.2–1.5s) no longer offsets it.** Net: wash on e350-class subs,
which is why grep's total ROSE while sort's fell.

`conv_diag` on sub_4d2a (new tree): `FIXPOINT NOT CONVERGED after 6000 rounds,
(no gap pair captured)` — identical to old (the 6000-iter cap is now
`src/cbat_vsa/cbat_vsa.ml:2802-2809`; degraded arm `src/hike_vsa.ml:66-90`).

## 4. Fixpoint internals (`Stages` adapter, vsa-debug build, converged subs)

stageprof output (saves the exact `STAGES`/`WALKS`/`GC` lines; runs:
`/tmp/opencode/rr-perf` vsa-debug build):

sub_9f00 (fixpoint ~0.9-1.0s):
```
STAGES: denote 0.871s/1378  join 0.091s/1948  equal 0.002s/1081
        widen 0.006s/43    walk 0.459s/608   scaffold 0.972s/975  glue 0.001s/1720
WALKS: pops 155648  blocks 155690  truncs 608  max_pops 256
GC: minor 275350478  major 6397570  promoted 6051798
```
Old → new, SAME sub: denote counts IDENTICAL (1378), join counts IDENTICAL
(1948), walk counts ~identical (608 vs 611) — but denote TIME 0.542→0.871s
(**+61% at identical call counts**) and minor words 212M→275M (**+30%**).
Per-denote cost rose: with self-seeding every def is denoted, none skipped.

sub_9570: denote 0.554/1284, join 0.153/1946, walk 0.354/483, scaffold 0.712/974;
WALKS 123648/123709/483/256; GC 217325130/5746811/5463486. Same shape.

sub_e350 (fixpoint ~4.4s):
```
STAGES: denote 3.996s/3724  join 0.415s/4704  equal 0.005s/2588
        widen 0.002s/63    walk 2.999s/1860  scaffold 4.422s/2353  glue 0.002s/4550
WALKS: pops 476160  blocks 476520  truncs 1860  max_pops 256
GC: minor 1255967388  major 39496342  promoted 37154836
```
`Stages.time `Walk`` wraps exactly the `refine_edge` call
(`src/cbat_vsa/cbat_vsa.ml:2418`, memoized per (block,target) under the solution
version at :2411-2427), nested inside `Denote` (:2829). So on the worst
converged sub: **refinement walks = 3.0s = 68% of fixpoint wall (75% of denote),
all 1860 walks truncating at the 256-pop cap** — the versioned `Walk_memo`
exists yet absorbs nothing at this truncation rate. Denote (transfer incl. its
inline refinement) = 90% of fixpoint; join ≈ 9%; widen/equal ≈ 1%.
`Stages.report` still never fires for non-converged subs (raise skips it).

## 5. `perf` on the worst (binary, sub) = (grep, sub_e350)

Three records on the new-tree binary (PID-attach + two `-- dune exec` wraps,
`-F 1000 --call-graph dwarf,8192 -e cpu_core/cycles/P -e cpu_atom/cycles/P`):
`/tmp/opencode/rr-perf-e350.data` (16,543 samples), `rr-perf-e350b.data`
(17,563), `rr-perf-9f00.data` (7,446). **All three fail dwarf unwinding on the
new binary: 0.4–0.7 chain frames per `stage_timer.exe` sample** (vs 12.9–17.7 on
controls below). The recorded format is byte-identical to working records
(`PERF_RECORD_SAMPLE(IP, 0x4001/0x4002)`, ~8KB dwarf dumps present), and
`perf report --no-children` resolves leaf symbols perfectly — only the
libunwind step fails, and only for frames inside the new binary (kernel/libc/
libLLVM/libgmp/cmxs frames unwind fine; 1,075/17,384 chained samples are all
C-stack).

Unwind-failure forensics (all negative except the last positive):
- Old binary, SAME workload, same CLI, same machine, today:
  `/tmp/opencode/old-e350.data` (rr-ctrl worktree @ fe8b411): **17.67
  frames/child-sample**; `/tmp/opencode/old-check.data` (sort sub_9f00):
  **12.9**. Environment exonerated; failure is binary-dependent.
- `.eh_frame` present in both (~69k FDEs each; sizes 0x2346e0 vs 0x236a30);
  `caml_apply2` FDE present with identical CFA program in both; neither binary
  stripped (both `with debug_info`).
- gdb unwinds the new binary fully and correctly — full 43-frame chain
  `ml_z_logand → … → denote_exp → denote_def → denote_block_with_stores_inner
  → stabilize_comps/scc → static_graph_vsa → offsets_of_sub (hike_vsa.pp.ml:53)
  → Stage_timer.entry → main`, incl. through `<signal handler called>`
  (OCaml stack-growth) frames. Unwind INFO is good; the consumer (libunwind
  via perf) fails on it. Mechanism undiagnosed — prime suspect is the
  `.eh_frame_hdr` lookup path (gdb doesn't use it; perf does); proposed test:
  `objcopy --remove-section .eh_frame_hdr` on a COPY (blocked only by BAP
  plugin env for direct execution — bare `.exe` can't find plugins, so the
  copy can't run outside `dune exec`; left as follow-up).

What the records still yield (no chains needed):

Flat top (`perf report --no-children`, cpu_core, whole 17.4k-sample e350 run
incl. project load; atom event: 45 samples, negligible — task pinned to P-cores):
```
 9.77%  caml_apply2               (closure dispatch plumbing; old: 10.19%)
 5.74%  do_some_marking           (GC)
 4.75%  Base.Map.find_2250
 3.40%  Base.Map.find_and_add_or_set_1368
 2.88%  Base.Map.change_2903
 2.72%  Base.Int.compare_324
 2.55%  Cbat_vsa.anon_fn[cbat_vsa.pp.ml:1373,16--689]  (= def_constraints body, src/cbat_vsa/cbat_vsa.ml:1308+)
 1.90%  caml_shared_try_alloc     (GC)
 1.90%  Base.Set.bal_743
 1.73%  alloc_custom_gen          (Zarith custom blocks)
 1.57%  oldify_one  1.29% pool_sweep  1.02% oldify_mopup  0.82% caml_alloc_small  (GC)
 1.48%  ml_z_shift_left  1.30% ml_z_addsub  0.80% ml_z_logand  0.59% ml_z_compare  0.56% ml_z_shift_right  (Zarith)
 1.23%  caml_apply3   1.02% caml_c_call
 0.97%  Bap_knowledge.find_exn (+ update_with/get/bind/upsert ≈ 5% combined — KB traffic, mostly load phase)
 0.85%  Bap_ir.compare_2266
 0.40%  Cbat_vsa.anon_fn[cbat_vsa.pp.ml:1288,7--1318]  (= cast-constraint helper, cbat_vsa.ml:1178-1261 region)
```
GC + allocation ≈ 14% of the whole run; Zarith ≈ 5%+; Map/Set/compare ≈ 15%.
**Every relevance symbol is gone** (`block_contributors`, `backward_slice`,
`Hike_vsa_relevance.*` — old: 40.6% inclusive + 2.71% leaf). `caml_apply2`
unchanged at ~10% (structural; flambda already on).

`perf stat` (stage_timer e350, `/tmp/opencode/rr-stat.err`): IPC **2.72**
(170.4G ins / 62.6G cyc, P-cores) — compute-bound, healthy; 206M core
cache-misses, 432M branch-misses, 248k minor / 0 major faults.

Inclusive `refine_edge` subtree check (via gdb sampling, since perf chains are
unavailable): 29 `bt` samples over 3 fixpoint-window runs
(`/tmp/opencode/rr-gdbstacks{,2,3}.txt`). The refinement subtree from the old
report is CONFIRMED LIVE on the new tree, twice with the full chain:
`refine_edge_inner_8053 (cbat_vsa.pp.ml:1367)` → `fixpoint_inner_123`
(`cbat_contextual_fixpoint.pp.ml:37`) → `Graphlib loop/step` → `f_156` (:34)
→ `def_constraints` anon `_8300` (2/9 samples in run 2; 1/7 in run 1).
Remaining samples: denote spine (`cap_at_width → create_inner → lift_binop/
lift_unop → denote_exp`; `create_inner → Cbat_map_lattice join fold`),
`Map.change`/`find_and_add_or_set`/`Set.add` recursion, `Sequence.loop` +
Graphlib `visit`, GC marking, one LLVM-disassembler load-phase sample.

## 6. Per-binary conclusions

- **sort**: sub_4d2a is down from 76.6% to ~35% of producer and from 10.4s to
  ~3.2s — the deletion removed the 7.5s backward slice, the ~3s
  non-convergence burn remains (degraded arm now emits 798 `Unbounded`
  seed-tags instead of zero tags). Rest of sort is converged subs at ~1s each.
- **grep**: cost is spread and UP ~44%: every converged-sub fixpoint got
  +33–44% (self-seeding denotes all defs; per-denote +61% at identical counts
  on 9f00) while the removed analyze lane (−1.5s on e350) only offsets the
  biggest sub. e350's 4.4s fixpoint is 68% refinement-walk burn (all
  truncating), 90% denote overall.
- The producer is still the majority of a lift (65–70% sort, ~50% grep).

## 7. Optimization candidates vs the new numbers (for the HTML re-rank)

1. **Backward-slice set/combinator cost — MOOTED (keep withdrawn).** The code is
   gone; `seed-detect` is 1–2ms. Its shape (Tid-keyed sets) transfers to the
   seeding walk only if that walk shows compare cost — it doesn't (no Map/Set
   anomaly attributable to seeding in the flat profile).
2. **Non-convergence burn — KEEP, smaller.** 3.2s/sub-class (was 2.75s but was
   76% of sort; now 35%), still 100% waste w.r.t. precision (Unbounded verdict),
   `conv_diag` still gapless. Prize shrank 10.4→3.2s.
3. **Inline edge refinement — KEEP, STRONGER.** Now directly timed (not just
   sampled): Stages `walk` 3.0s/1860 walks, all truncated = 68% of fixpoint on
   e350; gdb live-confirms the `refine_edge_inner → contextual-fixpoint →
   def_constraints` chain. `Walk_memo` (versioned, cbat_vsa.ml:2411-2427)
   exists but every walk still runs to cap — memo/skip-TOP/adaptive-cap shapes
   from the old report stand, now with a harder number.
4. **Allocation churn / GC — UPGRADE.** +30% minor words same-sub (212M→275M
   on 9f00); ~14% GC+alloc flat; Zarith ~5%+; denote time +61% at flat counts.
   IPC 2.72 says the core loop is healthy — the tax is heap traffic (Clp
   big-int temps + AI env joins), not stalls.
5. **`caml_apply2` ~10% — unchanged, structural, low actionability.**
6. **Forward lane — still nothing (the whole lane is 1–2ms of seed-detect).**
7. **NEW: self-seeding transfer tax.** Converged fixpoints +33–44% (e350
   3.052→~4.4s; 9f00 0.641→~0.9; 9570 0.547→~0.73) with IDENTICAL visit/join/
   walk counts — pure per-denote inflation (+61% on 9f00) from denoting every
   def. This is the measured price of the deletion and the entire grep
   regression. Any recovery must NOT reintroduce a pass or a gate (ADR-0003):
   candidate shapes are internal to the transfer — denote-memo hits on first
   visit, skip provably-uniform defs, or share denotation between the vertex
   path and the refinement re-walk (cf. `Transfer_memo`, cbat_vsa.ml:2832-2861,
   which currently only serves the vertex path).
8. **Extraction + stack model — DOWNGRADE.** Directly timed now:
   producer − fixpoint − seed ≈ 5–10% (~0.1–0.3s on the slowest subs). The
   quadratic-merge / repeated-walk shapes are real code but not where time
   goes; index/merge work belongs behind refinement, GC, and the tripwire.

## 8. Method notes (delta over the old report §8)

- Subtimes variance is ±10% run-to-run on this host (two runs per binary
  above); report ranges, not single samples. `stage_timer` reps vary ±5%.
- `perf record` wrap (`-- dune exec …`) and PID-attach give the SAME chain
  sparsity on the new binary — attach is exonerated; use whichever is
  convenient. Filter wrap records by comm (`stage_timer.exe` ≈ 99% of samples;
  `dune` parent + `objdump`/`ocamlc.opt` children are the rest).
- If dwarf chains come back empty (0–1 frames/sample) while leaf symbols
  resolve: suspect the binary, not the method. Controls that decide it fast:
  (a) `perf record` the fe8b411 `stage_timer.exe` (rr-ctrl worktree) on the
  same workload — 12–18 frames/sample here; (b) gdb `bt` on the live process
  (full chain here — exonerates unwind info); (c) compare `.eh_frame` FDE
  counts/sizes (`readelf --debug-dump=frames | grep -c '^0'`).
  Suspected interaction: perf's libunwind vs the new binary's `.eh_frame_hdr`
  lookup; untested (needs a runnable no-`.eh_frame_hdr` copy).
- gdb sampling recipe (fixpoint-window statistical profile without perf
  chains): launch probe in background, `sleep 6-9`, loop
  `gdb -p PID -batch -ex 'bt 6'` + `sleep 0.15` until the probe exits
  (~10–15 samples per 9s window; each attach pauses ~0.4s, extending the
  window). Classify stacks by content (load = LLVM-disasm/KB-create frames;
  fixpoint = cbat/denote/refine/Graphlib frames).
- `perf stat` needs no unwinding and is always worth grabbing (IPC/cache/
  faults sanity + P-core vs E-core placement: check the atom-event sample
  count — 45 here, i.e. firmly P-core).
- Old-binary reference (rr-ctrl @ fe8b411, run today):
  `stage_timer grep sub_e350` → producer 5.032 = analyze 1.635 + fixpoint
  3.396 (`/tmp/opencode/old-e350-out.txt`) — reproduces the old report's
  4.574 = 1.478 + 3.052 within ~10%; use it to sanity-check future deltas.
