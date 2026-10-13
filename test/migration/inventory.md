# Pin migration inventory

The one-time accounting for the test-redesign lane. The pre-redesign
suite lived in `test_cbat/`; it is retired. New pin ids are fresh
(`<MODULE>-NN`), so this file is the only link from the old files to the
new ones.

Disposition: **CARRIED** = every assertion re-expressed; **RETIRED** =
deleted with a reason. No row is RETIRED: every migrated module reported
zero retired checks.

## Per-module accounting

The old-site count is the number of `check`/`check_bound` assertions in
the source module(s); the pin count is the number of Alcotest groups in
the target. Folds (several old assertions inside one pin) and expansions
(one old table/loop producing one pin per row) are both expected; the
per-pin detail is in `test/pins/<module>.md`.

| old source | old sites | new target(s) | new pins | disposition |
|---|---|---|---|---|
| test_cbat/test_domains.ml | 200 | test_clp (111), test_exact (16), test_map_lattice (24), test_word (18), test_ws (31) | 200 | CARRIED |
| test_cbat/test_backward.ml + test_seed.ml | 56 + 22 | test_backward | 78 | CARRIED |
| test_cbat/test_sections.ml + test_regression.ml | 54 + 14 | test_sections | 68 | CARRIED |
| test_cbat/test_vsa.ml | 66 | test_vsa (61), test_call_effects (5) | 66 | CARRIED |
| test_cbat/test_forward.ml | 28 | test_forward (15), test_call_effects (10) | 25 | CARRIED* |
| test_cbat/test_wto.ml | 26 | test_wto | 31 | CARRIED |
| test_cbat/test_jump.ml | 43 | test_jump | 43 | CARRIED |
| test_cbat/test_model.ml | 39 | test_model | 39 | CARRIED |
| test_cbat/test_promote.ml | 13 | test_promote | 22 | CARRIED |
| test_cbat/test_bil2llvm.ml | 39 | test_bil2llvm | 22 (41 assertions) | CARRIED |
| test_cbat/test_resolve.ml | 20 | test_resolve | 20 | CARRIED |
| test_cbat/test_env_tag.ml | 17 | test_env_tag | 17 | CARRIED |
| test_cbat/test_properties.ml + test_landmarks.ml | 34 + 18 | test_integration | 19 (52 assertions) | CARRIED |
| test_cbat/test_fp.ml | 7 | test_emit_fp | 35 (64 assertions) | CARRIED |
| test_cbat/test_dce.ml | 7 | test_dce | 7 | CARRIED |
| zz_scratch_probe/clpequiv.ml | 1 | test_clp_equiv | 1 | CARRIED |
| test_cbat/test_main.ml, test_common.ml, test_fixtures.ml | infra | test/unit/harness.ml, common.ml, fixtures.ml | — | RELOCATED |

\* The label-based old-site count is not a pin count: one old `check`
can carry several labels (multi-condition assertions) and one string can
repeat. The migrated module's own report carries the authoritative
site→pin list.

## Reconciliation status

Resolved (T1). The divergences were artifacts of a label-based counter:
`check` calls are multi-line, `check_ir` helper calls were excluded by a
word-boundary count, and a `match Ok/Error` repeats one label across two
arms.

- `test_forward`: 26 counter hits → 25 logical assertions (the `Ok/Error`
  pair for E3-1 and for R-G1 each counts once) → 15 `FWD-*` + 10 `CE-*` =
  25 pins. Exact.
- `test_promote`: 15 `check`/`check_bound` + 7 `check_ir` = 22 logical
  assertions → 22 `PR-*` pins (T4-* 9, T10-* 5, PR-A* 6, PR-WC* 2). Exact.

`test_bil2llvm` is the one intended fold: 53 assertions (39 `check` + 14
`check_ir`) are carried as 41 assertion sites inside 22 `EMIT-*` pins,
with co-located `check_ir` calls conjoined — the module's own report lists
the fold. The other fourteen rows reconcile exactly.

Detail per pin: `test/pins/<module>.md` (concatenated into
`test/pins/`).
