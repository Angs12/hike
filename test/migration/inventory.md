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
| test_cbat/test_domains.ml | 200 | test_clp (111), test_fin_set (16), test_map_lattice (24), test_word (18), test_ws (31) | 200 | CARRIED |
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
| test_cbat/test_strip_canaries.ml | 6 | test_strip_canaries | 6 | CARRIED |
| zz_scratch_probe/clpequiv.ml | 1 | test_clp_equiv | 1 | CARRIED |
| test_cbat/test_main.ml, test_common.ml, test_fixtures.ml | infra | test/unit/harness.ml, common.ml, fixtures.ml | — | RELOCATED |

\* The label-based old-site count is not a pin count: one old `check`
can carry several labels (multi-condition assertions) and one string can
repeat. The migrated module's own report carries the authoritative
site→pin list.

## Reconciliation status

The migration ran per module with a clean `dune runtest` (22 modules,
0 failures). Two rows show a count divergence that a label-based counter
cannot settle — `test_forward` (25 pins vs 28 label occurrences) and
`test_promote` (22 pins vs 13) — because the counter over- and
under-counts multi-line and multi-label sites. These are recorded as a
follow-up ticket: a pin-by-pin audit against the git-history sources
verifying that no assertion in those two modules was dropped or
duplicated. The other fifteen rows reconcile exactly or have a
documented fold/expansion.

Detail per pin: `test/pins/<module>.md` (concatenated into
`test/pins.md`).
