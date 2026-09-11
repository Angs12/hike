# T16 — the decoder-deletion dig: the two defects between the jump pass and the VSA (P1)

Owner directives composed: the cond rewriter is THE jcc mechanism (the
VSA's flag-idiom decoding is redundant and goes); the removal must
change nothing on precision. The removal was ATTEMPTED at the T13
wire-up and measured **NOT precision-neutral: 17/37 -O0 red** — the
agent stopped per the acceptance conditional, reverted, and scoped the
dig. This ticket is the dig; **its landing act is the pipeline
registration of `hike-jump`** (constructed, pinned, currently
unregistered — commit `d607d02`).
Blocked-by: nothing, but it gates T5/T9's batteries only in the sense
that the tree is otherwise green without the registration.
Evidence: `.scratch/typed-model/tickets/T13-wireup-verdict.md` (the
17/37 measurement, the exonerations, the F2c experiment).

## The two defects (evidence-backed)

1. **The promotion reads pre-rewrite structure.** With `hike-jump`
   placed before `hike-vsa`, `out_variadic`'s promotion collapses to
   `sum_n(i64 0)` — `promote_sub`'s slot-arg correspondence consumes
   the BIR the jump pass has already rewritten (the stored-value
   structure it matches is gone/reordered). The construction question:
   does the promotion consume the JUMP-COMPILED BIR (the pass becomes
   the producer's first rewrite and the promotion matches the compiled
   forms), or does the pass run after the promotion (but then the
   analysis-order question returns — the wire-up measured 7+ red
   there, from defect 2)? The defects COMPOSE: fixing 2 alone was
   measured insufficient.
2. **The comparison-path bottom.** Feeding the BASELINE VSA walk
   compiled comparisons (no pass, no decoder change) bottoms a live
   two-loop head (the F2c experiment, reproduced under the merge-t10
   tree). The generic comparison rows + producer recursion route
   taken-edge constraints differently than the decoded-idiom rows did
   — a latent defect in the comparison path the decoded rows were
   papering over. The landmark machinery is exonerated (the F1 pins
   re-derived green over compiled comparisons).

## The mandate (architecture-side; the corpus is the acceptance)

Diagnose defect 2 to mechanism FIRST (it is the deeper one: the
comparison path's taken-edge routing must be as exact as the decoded
rows' — whatever invariant the decoded rows exploited, the comparison
rows must provide it by construction). Then resolve the ordering
(defect 1) in the direction that makes the pass the producer's first
rewrite with the promotion consuming compiled structure. Then
RE-ATTEMPT the decoder deletion with the corpus as acceptance:
strict -O0 37/37, the pin at 6, convergence line-identical, F1 green,
referee 0 — the deletion lands only at full green; any residual cost
is inventoried for the owner.

## Battery protocol (you hold the shared plugin slot)

Same as T1's (see `T1-opt-safety-regression.md` §Battery protocol):
`eval $(opam env)` first; `record_provenance.sh` after every install;
battery artifacts on home disk (`/home/tovpr/tm-battery/t16/`); never
`/tmp`.

## Acceptance

- `hike-jump` REGISTERED (first-in-chain) with strict -O0 **37/37**,
  strict opt-safety 37/37, the pin at 6, convergence line-identical,
  F1 green, referee 0, the suite ALL GREEN.
- The VSA's flag-idiom decoder deleted (the total-removal scope: code,
  comments, docs) — or, if a genuine residual remains, the inventoried
  cost with the owner's decision point.
- The optimizability numbers re-measured (the prize: fn_table_disp
  280→143 already demonstrated).
- Verdict: the two mechanisms' diagnoses, the fixes' case-count delta,
  the full gate table, the census.

Worktree: `/home/tovpr/hike-t16`, branch `tm/t16-decoder-dig`.
