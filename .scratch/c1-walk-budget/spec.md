# C1 — Walk-Pop Budget (per-SCC recharge, dynamic cap)

**Status:** spec (approved by grilling 2026-09-05; implementation NOT started)
**Tree:** `e4b309c` (main, post review3-removals merge)
**Supersedes:** nothing. **Related:** ADR-0002 (single-pass trace partitioning —
the deep walk runs inline at every conditional jump; this spec BOUNDS its cost,
it does not change its placement), ADR-0006 (the def-table kill — C6's grave;
this is the re-ranked next target).
**The review:** `/tmp/opencode/architecture-review-20260905-0130.html` (C1 card,
post-merge numbers).

---

## 1. Problem (the measured fact base)

The deep backward walk (`refine_edge`, `src/cbat_vsa/cbat_vsa.ml:1480-era`)
runs inline at every conditional jump of every block denotation (ADR-0002),
bounded by `~steps:256` (`Cbat_contextual_fixpoint.fixpoint`). Measurements on
the post-merge tree (`3870295`):

- grep `sub_e350` (the worst converged sub): walk lane = **2.61s of 3.53s
  fixpoint (74%)**, 1,826 walks, **ALL truncating at the 256-pop cap**, 467,456
  pops — ~256 pops per walk, every one.
- sort whole-binary: 508k pops over 1,091 truncated walks; the corpus
  fixtures' pops are 3 orders smaller (their walks terminate naturally well
  below 256).
- The `Walk_memo` hit rate is 38.9% (stable pre/post-merge) — during the
  ascending phase a read block's version bumps almost every round, so the
  memo cannot absorb the load.
- A walk that truncates at 256 has spent its pops discovering constraints the
  cap then discards — truncated walks are SOUND (proven by the corpus gates
  over months) but their pops beyond the natural fixpoint need are waste.

**The seed-skip alternative is DEAD (grilling round 1, unsound):** "skip the
walk when no Var seed's meet changed env" is WRONG because a no-op seed can
still produce new cell meets when propagated backward through a Load def or a
Load-valued phi (`constrain_cell_on_trace` inside the walk). Recorded so it is
not re-proposed: the identity rule must not be seed-local.

## 2. The design (grilling-settled, 10 questions)

**One mechanism: a per-run walk-pop budget with a dynamic cap.**
(C8 2026-09-05: was per-SCC; the recharge trigger moved to fixpoint start —
item 2. The cap machinery — item 4 — is unchanged.)

1. **The allowance:** `N = C × (out-edges of the SCC's member blocks)`, with
   `C = 1024` (conservative start; the A/B decides).
2. **The lifetime:** per-run. The budget refills **once at fixpoint
   start** (`N = 1024 × the whole sub's out-edges`) — NOT per SCC.
   (Amended by C8 2026-09-05: the per-SCC `stabilize_scc`-entry trigger
   died with the recursive driver. A worklist has no "stabilization
   episode" event — blocks visit and re-visit individually as successors
   change, so there is no per-SCC entry point left for a refill to hang
   on; per-SCC allowances would have nothing to refill on. The single
   per-run recharge keeps the same shared cell, the same `budget_per_edge`
   constant, and the same dynamic-cap enforcement.)
3. **The cell:** an `int ref` in `Cbat_runctx.refine_ctx` — a new field
   `rc_walk_budget`. `refine_ctx` records are copied per memo-store
   (`{rc with ...}`); a `ref` field SHARES the cell across copies — exactly
   the single-shared-cell semantics wanted (one budget cell per run).
4. **The enforcement — memo-first, dynamic cap (UNCHANGED by C8):**
   - the `Walk_memo.find` lookup runs FIRST (a hit is a free, real refinement —
     never refuse free precision);
   - on a miss, the walk launches with `~steps = min (256, !budget)`;
   - **the walk is NEVER skipped at launch** (no all-or-nothing cliff): a
     budget of 40 runs a 40-pop walk, not a zero-pop one;
   - as the walk pops, it decrements the shared cell (one decrement per
     Graphlib step — VERIFY one step == one pop from BAP's graphlib source
     before writing the decrement; the verification is ticket 01's first
     task);
   - a budget-limited walk is NOT memoized (no identity entry with an empty
     read-set — even though it would be run-consistent, it is a trap for
     future readers);
   - at budget ≤ 0 the miss path still runs a `~steps:0`... **no** — `min(256,
     0)` would launch a zero-step walk; the spec resolves this as: the
     launch uses `max (min (256, !budget)) 1` when the budget is > 0, and
     once `!budget <= 0` the walk runs with `~steps:1` (the identity-floor:
     the walk still enters the guard block — its own-def walk — preserving
     the seed block's local refinement, which is the one part the seed-meet
     fold did not do). This is the graduated floor; the A/B's tag-stability
     gate decides whether it holds.
5. **Instrumentation:** extend the `Stages` walk counters
   (`cbat_vsa_stages.mli` + both adapters): `budget_hits` (walks shortened
   by the budget) and `pops_saved` (the pop delta vs the 256 cap) — vsa-debug
   only, the production adapter stays a no-op (principle #6).
6. **Soundness statement (one line):** a shorter walk is a sound coarsening —
   the design has ALWAYS accepted truncated walks (the 256 cap is the proof);
   the budget only chooses WHERE the cap lands. NO gates, NO skips, NO
   bottom — principle #2/#3 compliant.

## 3. The acceptance bar (grilling Q10)

The landmark-widening precedent class: **the gates, not byte-identity, are
the oracle** (IR WILL differ on the real binaries if the budget binds — a
truncated walk is sound but different).

1. Unit suite: `dune runtest` — all existing checks PLUS the three new
   fixtures (below) green.
2. Corpus 35/35 rc=0 (32 fixtures + sort/grep/gcc-12), `check_allocas`
   identical-failure-class to control (the 3 pre-existing shape-d fails).
3. BOTH semantic gates: same PASS/FAIL lists as the control
   (`run_semantic_all`: 30/5 with the same 5; the 8-bin oracle 8/8).
4. **The tag-stability gate (NEW):** per-sub tag counts AND kinds on
   sort/grep/gcc-12 IDENTICAL to control (`subtimes` per-sub `tags` column +
   `dump_tags`/`memostats` kinds). If tags move more than marginally, raise C
   before landing (1024 → 4096) or accept and re-baseline explicitly — the
   decision point is recorded in the A/B.
5. A/B producer timing: 2+ rounds × 3 binaries, interleaved (host ±15%),
   stage counters attributing: `walk` seconds DOWN, `pops` DOWN, `denote`
   counts flat (the budget touches only walk pops, not visit counts).

## 4. Fixtures (grilling Q10 — the F1-BUDGET family)

In `test_cbat/test_seed.ml`/`test_backward.ml` (the F1-NEQ/F1-FT precedent
class — constructible through the existing seams):

- **F1-B1 (soundness):** a small loop sub; the budget cell set tiny via the
  rctx ref directly (the test constructs the context); the walk still
  returns a SOUND refinement — the seeds' own meets survive and the cell
  meets are a SUBSET of the unlimited result (compare with `⊑`, not `=`).
- **F1-B2 (recharge):** a two-SCC sub; both SCCs receive their full allowance
  (the second SCC's walks are NOT starved by the first's spending).
- **F1-B3 (memo-first):** a memo hit still returns the cached refinement
  even when the budget is exhausted.

## 5. Files (the map; re-locate by name, lines drift)

- `src/cbat_vsa/cbat_runctx.ml` — `refine_ctx` gains `rc_walk_budget : int
  ref`; `mk_rctx` initializes it (a fresh cell, contents = max_int: unused
  until a recharge sets it).
- `src/cbat_vsa/cbat_vsa.ml` — the recharge site (fixpoint start, C8: was
  `stabilize_scc` entry; the whole sub's out-edge sum via `rc_out_edges`,
  computed ONCE per run);
  the walk site (`refine_edge`'s caller in `refine_edge_inline`: memo-first
  order preserved, the `~steps` becomes the dynamic cap, the shared decrement
  hooks into the walk's pop accounting, and the budget-limited walk skips the
  `Walk_memo.add`).
- `src/cbat_vsa/cbat_vsa_stages.mli` + `_debug_src.ml` + `_prod.ml` — the two
  new counters.
- `test_cbat/test_seed.ml` (or `test_backward.ml`) — the F1-B* fixtures.
- `zz_scratch_probe/` — no new probes (memostats/stage_timer already count
  walks; the budget counters ride the existing STAGES line).

## 6. Deliberately NOT in this spec (recorded rejections)

- The seed-skip identity (unsound — the cell-meet leak; §1).
- Graduated per-walk caps as the primary mechanism (subsumed by the dynamic
  cap's `min` + the floor).
- Per-round recharge (would not bind on multi-round subs — gives back the
  win).
- Budget-first check order (refuses free memo hits).
- Memoizing skipped walks (the empty-read-set trap).
- Whole-sub edge counts per SCC (a monster SCC in a big sub gets the
  full-sub allowance — the budget barely binds exactly where it should).
- ADR-0006's def table (dead by measurement, separate lane).
