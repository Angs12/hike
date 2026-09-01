# 03 — the change-driven cache for the inline deep refinement

**Status:** DONE (reopened 2026-09-01 per the user's mandate "18 secs for
the corpus is toooo long... it should run on bigger binaries!" — the
big-binary wall was 40-80 s; landed on `wt-03` commit `f5d830d`, see
`/tmp/opencode/single-pass-trace-partitioning/report-03.md`).
**Depends on:** 02 ✅
**Blocks:** none

**The landed result:** ls 39.0s→17.0s (−56%), sort 68.6s→21.6s (−69%),
df 46.5s→15.3s (−67%), the 32-binary corpus ~18-28s→9.0s total — ALL
emissions BYTE-IDENTICAL to the pre-cache baseline (the corpus's 32
`.ll`+err+stdout+rc AND the three big binaries' 18/9/7 MB `.ll`+err).

**The design as landed — one deliberate deviation from the ticket's
literal key (a SOUNDNESS fix; the full argument is in the report and in
the `[refine_ctx]` comment block in `cbat_vsa.ml`):** the ticket's
"OUT-state + edge-cond suffice — AI.equal on the OUT-state" is NOT sound
for this walk: the walk reads the SOLUTION at UPSTREAM blocks (the
producer subtraction `denote_def d (Solution.get sol (Term.tid blk))`
and the trace-exact cell meets), and upstream states WIDEN mid-fixpoint,
so an OUT-state-only key would reuse results computed against narrower
upstream states (unsound narrowing — the array_local class). The landed
key: per-(source block, jmp tid) entries validated against the per-block
SOLUTION VERSIONS of the walk's READ-SET (the visited blocks) — and the
engine's `set` fires only under `not (AI.equal old new_val)` (the
stability gate), so version-identity IS the AI.equal-identity of every
read state: the ticket's own model — the widening head's
`AI.equal old (AI.join old incoming)` check — hoisted to O(1) per lookup.
The cache unit is the WALK ONLY: the seed derivation and the gated env
meet run every visit (the meet's empty-meet arm is the landmark
ACQUISITION seam — skipping re-acquisitions after `lm_advance` would
flip `lm_calc_steps` Finite→Zero and change the widening arm).

Original acceptance criteria:
- [x] Per-edge deep walk cached; re-runs only on input change (the
      read-set's per-block solution versions — the sound form of the
      OUT-state `AI.equal` check; the source block is pre-seeded into
      the read-set, so its env input is covered by the same mechanism).
- [x] Corpus emission byte-identical to 02 (ALL 32 `.ll` + err + stdout
      + rc; ALSO byte-identical on /usr/bin/ls, /usr/bin/sort, /usr/bin/df
      — 18,358,663 / 8,977,622 / 7,137,927 bytes of IR, plus their err
      logs — the strongest form of the no-precision-change gate).
- [x] Measurable cost reduction on a representative binary (−56% to
      −69% wall on ls/sort/df; the hot sub's fixpoint −80%; the corpus
      total −50%+).
