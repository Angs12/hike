# T4b — conversion correctness: the struct-copy + indirect-call classes (P0)

Spec: `.scratch/typed-model/spec.md` — binding constraints + the
ARCHITECTURE-SIDE doctrine (the fix's diff must DELETE cases, not add
them). Parent: T4 (the grilled conversion, merged `9b06689`).
Blocked-by: nothing (it IS the conversion-correctness blocker).
Blocks: T5/T9's measurements (their numbers are meaningless until the
-O0 oracle is green).

## The measured failures (the T4-merge battery, `/home/tovpr/tm-battery/merge-t4/`)

- **-O0 strict 32/5** (37-bin corpora): `nested_struct`, `sret_big`,
  `struct_by_value` — ONE class, watchpoint-diagnosed in T4's verdict:
  the lifted i128-overflow guard skips `build`'s copy; plus the TWO NEW
  T4 sources `fn_escape` and `fn_table_disp` — the thunk /
  pointer-call / window path has a conversion hole for exactly the
  classes they were written to exercise.
- **-O2 pinned 28/9**: the standing four (byte_copy, union_overlap,
  va_arg_mixed, va_arg_vacopy) + regressions `fizzbuzz_safe`,
  `spill_many` + the new `fn_table_disp`, `jump_table_sw`, `fn_escape`.
  T4's claimed va_arg_vacopy improvement did NOT reproduce on the
  merged tree — re-attribute under the merged model.
- opt-safety 32/6 (+array_local under opt).

The -O0 primary oracle being red makes this the program's ONLY
priority: the conversion is not "correct" until the classes it created
are constructed away.

## The mandate (architecture-side, per the owner's doctrine)

- **The struct-copy class**: the failure is the INTERACTION of the
  i128-overflow alignment-guard lane with the promoted copy path — the
  guard arm must carry the copy BY CONSTRUCTION (one general rule over
  the access kinds, total per tag kind), not a special case for
  `build`'s shape. If the guard lane and the promotion disagree about
  who services a wide access, the architecture answer is ONE owner of
  every access — restructure the dispatch, never add an "if copy then
  skip guard" case.
- **The indirect-call -O0 class**: `fn_escape`/`fn_table_disp` exercise
  thunks, pointer calls, and the window materialization; find the
  broken rule (a promotion whose correspondence is wrong at -O0, a
  thunk whose unpacking mismatches the packed layout, a window base
  that doesn't name the caller's cells) and fix THE RULE — the general
  one, at the point where the wrong value is produced.
- **Re-measure after**: strict -O0 must reach 37/37; the regressions
  (fizzbuzz_safe, spill_many) likely share the root cause — if they
  flip back, the pin shrinks; whatever remains is re-attributed in the
  verdict. va_arg_vacopy's -O2 symptom re-attributed under the merged
  model (it may be a different failure than the recorded one).

## Binding constraints

NO GATES, NO FALLBACKS, one mechanism, ARCHITECTURE-SIDE FIXES (the
diff deletes cases), soundness over precision. Hard bars: builds both
profiles, blocker clean, referee 2,861,148/0, runtest failure set ==
the 8 baseline + named inventory. The verdict carries the case-count
delta of the fix diff.

## Battery protocol (you hold the shared plugin slot)

`eval $(opam env)` first; `record_provenance.sh` after every install;
battery artifacts on home disk (`/home/tovpr/tm-battery/t4b/`). The
corpora at `/tmp/corpus*` are NOW 37 bins (T4 rebuilt them in place —
against its isolation instruction; the canaries pass, the state is
recorded); USE them (they are the battery's corpora) but NEVER
`compile_corpus.sh` into `/tmp` again — if you need a rebuild, rebuild
BOTH lanes into your own dirs and update nothing global.

Gates every iteration: `dune runtest`, -O0 emission 37/37 rc=0,
check_allocas green, strict -O0 semantics → 37/37 (THE goal), strict
opt-safety → all PASS or inventoried, -O2 emission 37/37, the pinned
gate vs the current golden nine — the set may only SHRINK (proven
flips); growth blocks. Convergence vs `/home/tovpr/tm-battery/
merge-t4/conv.log`.

## Acceptance

- Strict -O0 semantics **37/37** — the primary oracle restored.
- The struct-copy class and the indirect-call -O0 class are dead by
  construction (the general rules named, the case-count delta shown).
- The pin: the golden nine re-attributed (shrinks are proven flips;
  the golden + AGENTS.md move in the merger's commit).
- Verdict: per-class mechanism (what was constructed), the case-delta
  accounting, the full gate table, the re-measured -O2 set with each
  member's attribution, the convergence rows.

Worktree: `/home/tovpr/hike-t4b`, branch `tm/t4b-conversion-correctness`.
