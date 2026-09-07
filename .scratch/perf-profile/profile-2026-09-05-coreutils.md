# Perf profile: hike lifting coreutils-9.6 (all 103 binaries)

Date: 2026-09-05. Host: 13th-gen Intel i7-13700H hybrid (P-cores 0-11 @
4.8GHz, E-cores 12-19 @ 3.7GHz), 15GB RAM, 20 threads. perf 7.1.12,
`kernel.perf_event_paranoid = -1`. Tree: **main @ 753601b** (C8 worklist +
C1 walk-budget + review3-removals all merged), plugin installed from THIS
tree, provenance verified (bundle sha16 `1e095b7b973fa695`, byte-identical
rebuild confirmed). Coreutils: GitHub master shallow clone, built
`-O0 -fno-stack-protector` plain-gcc = **PIE executables** (103 collected,
all ET_DYN — the X1-d absolute-immediate class is structurally absent).

Method: `perf record -F 1000 --call-graph dwarf` per binary (serial, one at
a time — parallel lifts OOM the box), then `perf script` → anchor-based
phase attribution (`agg.py` in this dir; anchors = the current post-ADR-0003
symbol vocabulary: stabilize_worklist/denote_block (fixpoint),
refine_edge/Cbat_contextual_fixpoint (walk), Cbat_clp/Zahlen/GMP (ai_domain),
Hike_stack_model (stack_model), Bap_disasm/objdump (frontend), …).
Wall-times re-measured CLEAN (no perf, idle machine) for every binary.
Per-sub costs via `subtimes.exe` (production `offsets_of_sub` timing) and
`stage_timer.exe` (vsa-debug build: denote/join/walk/GC counters) on the
idle machine only.

## 1. Headline: every coreutils binary lifts, rc=0, 103/103

| metric | value |
|---|---|
| binaries lifted (rc=0) | **103/103** |
| clean lift wall (total) | **803s (13.4 min)** |
| clean lift wall (mean / median / p90 / max) | **7.8s / 5.2s / 16.8s / 30.4s** |
| fast quartile (p25 / p50) | 4.2s / 5.0s |
| slowest: du | 30.4s; ptx 21.4s; cksum 21.4s; stat 20.4s; vdir 19.9s |
| total emitted IR | 380 MB (mean 3.7 MB; max cksum 23 MB) |
| perf samples captured | 176,957 (183 samples/s of clean wall) |
| whole-corpus throughput | **~7.6 binaries/min serial** (one core) |

P-cores vs E-cores measured on du: P 30.3s vs E 58.0s (1.9×); the scheduler
kept everything on P-cores (cpu_atom carried 10/30517 samples). Pin lifts
to P-cores in any batch driver for reproducible numbers.

## 2. Where the time goes (perf phase attribution, 103 binaries)

Uncontaminated window (80 bins, order 24-103, 105,959 samples; the a-d
alphabetical prefix ran ~2× walls because my own debug probes were
competing on E-cores during it — sample DISTRIBUTIONS valid throughout):

| phase | share | what it is |
|---|---|---|
| **ai_domain + gmp_zahlen** | **31.6%** | Cbat_clp/Zahlen arithmetic + GMP limbs (`ml_z_sign`, `Z.sub`, `__gmpn_rshift/sub_n/lshift`); callers: `Cbat_clp.finite_end`, `Cbat_word_ops.factor_help`, `Cbat_clp.create_inner` |
| sys + other | 29.3% | unattributable: kernel page faults (asm_exc_page_fault 3.2%, the GC's minor-heap page churn), malloc/free, DWARF-lost [unknown] frames |
| **fixpoint engine** | **14.0%** | stabilize_worklist → denote_block_with_stores transfers (worklist driver + memo glue) |
| dynlink | 6.0% | bap loading ~10 plugins per invocation (ld.so + Dynlink_common) — fixed startup tax, not per-binary work |
| stack_model | 4.8% | Hike_stack_model regions/plan — `merge_loop`'s `components_overlap` quadratic region merge |
| refine_walk | 3.8% | the inline backward walks (pp:1357 lambda = walk transfer) |
| frontend_lift | 3.8% | BAP disasm+lift (objdump child = 0.1% of samples; negligible) |
| gc + ocaml_runtime | 4.0% | OCaml GC (do_some_marking, pool_sweep) + runtime |
| emit (bil2llvm) | 1.3% | |
| stl_pass + dce_pass + filter | 1.1% | |

**Producer (VSA) total = 54.3% of a full lift**; everything else is BAP
frontend, pass machinery, GC, and the emit/dce/stl tail. The VSA producer's
own split, measured clean on 7 bins: producer = 42-59% of lift wall
(mean ~47%), confirming the perf attribution.

## 3. Per-sub distribution (subtimes, production path)

The producer cost is **gnutail-dominated**, flat-tail: the top sub takes
25-47% of producer time, and ~90% of subs cost <100ms each.

| binary | subs | producer | top sub |
|---|---|---|---|
| du | 761 | 15.1s | `__strftime_internal` 3.85s/25% (686 blk, 7940 defs, 1173 tags) |
| stat | 476 | 12.0s | `__strftime_internal` 2.74s/25% + `vasnprintf` 2.45s/22% + `printf_fetchargs` 1.90s/17% |
| cksum | 520 | 9.9s | `blake2b_compress` 1.99s/20% (12654 defs in 395 blk — fully unrolled crypto core) |
| ls / vdir / dir | 707 | 9.0-9.9s | `__strftime_internal` 2.76-2.96s/31% |
| sort (system) | 452 | 7.6s | `sub_4d2a` 6.08s... **now converges** (609 real tags vs 2026-09-04's 0-tag degraded burn — the C8 worklist fix visible end-to-end) |
| grep (system) | 475 | 11.5s | `sub_e350` 3.37s (vs 4.61s on fe8b411 = −27%) |
| csplit/nl/tac/expr/ptx | ~500 | 9.3-9.8s | `quotearg_buffer_restyled` ~1.0s/11% (the regex/quotearg gnutail) |

Cross-cutting worst-sub classes: `__strftime_internal` (the date/time
formatter, 686 blocks/7056 defs) is the single worst sub in 5 of the top-10
bins; `quotearg_buffer_restyled` (383 blk/3248 defs) leads the regex-heavy
gnutail; `blake2b_compress`/`sm3_process_block` (cksum's checksum cores)
are def-dense unrolled loops.

## 4. Fixpoint internals on the worst sub (stage_timer, vsa-debug, idle)

`__strftime_internal` (du's and ls's #1):

| stage | time | counts |
|---|---|---|
| producer (offsets_of_sub) | 2.77s (ls) / 3.85s (du) | |
| fixpoint (stabilize_worklist) | 2.28s / 3.21s | |
| denote (transfer) | 2.18s / 3.05s | 1939 (ls) / 2504 (du) transfer calls |
| join | 0.05s | 2536 |
| walk (inline refines) | 1.25s / 1.97s | **935/1079 walks, ALL truncated at the 256-pop cap**; 239k/276k pops total |
| widen | 0.001s | 7 (landmark widening is now ~free) |
| GC | — | minor 653M words / promoted 17.7M (ls); 952M/30.3M (du) |

Every heavy sub shows the same shape as the 2026-09-04 baseline (denote 70-80%
of fixpoint; walks all truncating) — but the absolute values dropped: grep's
sub_e350 producer 4.61→3.37s, e350 walk pops 467k→236k (the C1 budget halving
visible), and sort's sub_4d2a now converges (C8). Transfer_memo hits: ls
sub_4bbd 49.7% / grep sub_e350 24.8% (a stale-rate of 28.9%/46.2% — the
memo invalidation still discards half the work).

## 5. Diagnostics across the corpus (all benign classes)

| class | count | note |
|---|---|---|
| undef-read (never-defined model-ABI lanes) | 68,670 | R9/R8/RCX/RSI read before write — the lifted-entry ABI-lane pattern, modeled [undef]; 19k are per-sub summaries |
| guarded: Unbounded stack access | 38 | re_string_reconstruct / build_wcs_* (indexed RBP+RAX stores, TOP by design), copy_internal (RSP,el dynindex) — sound fallback to memory |
| vsa: fixpoint not converged | **1** | `cksum_avx2` (2948 blk): burns the 6000-visit backstop, degrades to Unbounded (sound). NOT deterministic: a fresh subtimes run converges with 479 tags — it sits ON the backstop boundary; conv_diag cannot capture the gap pair (the raise passes None) |
| unmapped intrinsic | 4 | `fconvert_rne_ieee754_binary_32` (ftoastr ×2), `cast_sint_rne_ieee754_binary_32` (double_to_human, tail_forever_inotify) — fp-conversion stubs external; poison result lanes |
| 100%-tag invariant gaps | 0 | every stack access carries vsa_info |

## 6. Optimization candidates, ordered by measured prize

1. **Arithmetic domain (Candidate B: Cbat_word substrate — LANDED 2026-09-07)** —
   replaced BAP's boxed `Word.t` with `Cbat_word.t = Small of int | Big of Z.t`
   across `Cbat_clp`, `Cbat_word_ops`, `Cbat_fin_set`, `Cbat_clp_set_composite`.
   Real fixpoint census on `ls` measures **91.9% of operands** (33,983 / 36,994)
   hitting the immediate unboxed `int63` fast path (0 allocations). Validated
   with 2.86M `clpequiv` checks (0 mismatches), 32/32 corpus IR byte-identity,
   and 32/32 semantic equivalence.
2. **Transfer/join engine (14.0%)** — denote's 70-80% share is mostly
   `denote_exp` re-walking BIL into the domain (caml_apply2 3.5% flat
   overall; Map.find 1.6%). The Transfer_memo halves it (49.7% hits on ls)
   but 28.9-46.2% stale-rate means version-keyed invalidation discards
   reusable entries.
3. **GC/page churn (sys 29.3% incl. 3.2% page faults)** — 0.65-1.2 BILLION
   minor words per heavy sub (653M for ls's strftime at 2.8s ≈ 230M words/s).
   OCAMLRUNPARAM `s=8M` is already set by the pipeline; big-alloc reduction
   in Clp/Zahlen paths attacks both this and #1.
4. **stack_model merge_loop (4.8%)** — the `components_overlap` quadratic
   pairwise region merge (`exists_17538` is 5.2% of all late-window samples
   on its own, the single hottest hike symbol in the corpus). Sort-and-sweep
   would break region-id determinism (IR re-baseline, not a rider).
5. **Dynlink tax (6.0%)** — 10 plugin dynlinks per bap invocation (~0.3s);
   batch lifts under one bap process amortize it entirely if a driver ever
   wants another ~1.5× on small binaries.

## 7. Environment facts that bit this session (recorded for reproducibility)

- **Perf wall ≠ clean wall**: `perf record --call-graph dwarf` costs
  ~5-20% wall; my concurrent debug probes during the a-d prefix cost
  ~2× on those bins. Sample shares are cycle-accurate regardless; walls
  are from the clean serial re-run (`clean_times.tsv`).
- Hybrid cores: an unpinned lift lands on P-cores (verified: 10 atom
  samples / 30517); pin `taskset -c 0-11` for stable numbers.
- Reboot wiped tmpfs (corpus + clone) once mid-session; coreutils rebuild
  (bootstrap+configure+make -j20) ≈ 12 min. Artifacts now mirrored to
  `.scratch/perf-profile/` in the repo.
- `objdump` (BAP's disassembler backend) is a CHILD PROCESS but costs
  0.1% of samples — the frontend is OCaml-side (Bap_disasm glue), not
  objdump-bound.
