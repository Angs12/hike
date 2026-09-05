# Kill the per-sub static def table (review-3 candidate C6) — dead by measurement

## Decision

The proposed **per-sub static def table** (hoist `denote_def`'s frame-independent
prologue — `Var.typ` resolutions, free-var lists, rhs shapes — into a
`rc_def_table` built in `mk_rctx`, consumed by the forward fold and the walk's
re-denotes) is **REJECTED on post-merge measurement** and will not be built.

## The measurement (2026-09-05, post-merge tree `3870295`, /usr/bin/sort, perf
cpu-clock, call-graph dwarf, `/tmp/opencode/perf-arch-10/prologue2.data`)

`denote_def`'s **self time is 0.10%** of wall; the components a static table
could hoist sum to **~0.2%**:

| symbol | inclusive | note |
|---|---|---|
| `Cbat_vsa.denote_def` | 13.43% | but **0.10% self** — 99% is `denote_exp`'s CLP ops |
| `Cbat_ai_representation.frame_lookup` | 0.07% | the assoc-list frame lookup |
| `apply_frame_def_list` | 0.07% | the frame advance |

What IS expensive inside `denote_def` — `lift_binop` 12.07%, `Clp.create_inner`
5.75%, `Base.Map.find` 3.52% — is the **value-domain arithmetic itself**
(`denote_exp`'s body): dynamic values, not hoistable by any static table. That
cost belongs to the hash-consing (C2) and int64-CLP (C7) lanes.

## Why the original premise was wrong

The review measured the candidate against a **pre-merge** tree and cited the
"+33–44% converged-sub fixpoint slowdown at identical visit counts" from
`.scratch/perf-profile/profile-2026-09-04-rr.md` §7 as the recovery target.
That tax was the price of denoting **every** def after the relevance deletion
(ADR-0003). Two things have since absorbed it:

1. **The live-in GC** (merged in `a9a1a8b`, review-3 candidate 9): dead
   virtual temps are dropped from every transfer result before the join, so
   each denoted def's downstream cost shrank — joins fell 3× (0.57s → 0.17s on
   grep sub_e350) at flat call counts.
2. The relevance tag check itself — the per-def `Term.has_attr`
   (`Univ_map.find`) that motivated the "relevance flag in the table" field —
   was **already deleted** by rr-02/ADR-0003: `denote_def` on this tree checks
   no tag at all.

The grilling settled the design (narrow static-only scope, `rc_def_table` in
`Cbat_runctx`, positional indexing, minimal three-field entry, full
byte-identity + A/B timing bar) — and the fresh profile then showed the
hoistable ceiling (~0.2%) sits below the host's ±15% measurement noise. A
table that cannot measure its own win is complexity for nothing (the
whole-map produced-value memo precedent: reverted at +18%).

## Considered options

- **Narrow static-only table (the grilling's Q1 answer)** — rejected by the
  measurement above: the ceiling is ~0.2% of wall.
- **Wide table with a frame-version key caching the frame rewrite** —
  rejected: the frame rewrite is genuinely dynamic (depends on the abstract
  state's frame relation); a frame version is only cheap to compare after
  hash-consing (C2), which is a different candidate's prerequisite.
- **Build it anyway to serve the walk's re-denotes** — rejected: the walk's
  re-denotes call the SAME `denote_def`, so the same 0.2% ceiling applies
  (the walk is 74% of fixpoint, but that cost is walk POPS and CLP meets,
  not the denote prologue).

## Consequences

- No `rc_def_table`; `mk_rctx` keeps its current fields.
- The `denote_def` prologue stays as-is: `frame_rewrite_rhs`/`rewrite_addr`
  (2 top-level pattern matches each), `Var.typ`, the `Exp.free_vars` in
  `derived_free` — all measured near-zero post-merge.
- The domain-op cost (`lift_binop`, `create_inner`, Map/Set churn) is the
  property of the **C2 hash-consing** and **C7 int64-CLP** lanes, not of a
  static table; future sessions chasing it should go there.
- Next perf target per the same grilling: **C1, the walk identity fast-paths**
  (74% of fixpoint on grep's worst sub, all walks truncated at the 256-pop
  cap).
