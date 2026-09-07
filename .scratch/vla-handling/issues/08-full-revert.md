# VH-08 — Full revert of the affine lineage (keep P6 + P3)

**Status:** in-progress (worktree /home/tovpr/backup/wt-vh08)
**Depends on:** none (supersedes the ladder: VH-01..VH-05, VB-01..VB-06 remainder)
**Blocks:** none

**What to build (decision 2026-09-04: full revert, ledgers in `../affine-value-ledgers.md`):** remove the entire affine apparatus and restore the 344d825 vocabulary — delete `cbat_affine.*`, `cbat_var_order.*`, `test_affine.ml`, `test_var_bounds.ml`, `test_vla.ml` (and their dune stanzas/registrations); revert `cbat_vsa.ml`, `cbat_ai_representation.*`, `convutils.ml`, `hike_stack_model.ml` (VLA/floor/solver/verdict/spill/arms hunks), `hike_vsa.ml`, `hike.mli`, `bil2llvm.ml`, `test_regression.ml`, probes. KEEP exactly two hunks: (1) the P6 double-negation frame fix (`expr_of_term` PLUS-with-negative-scale, `a50a044` + its pin test — reverting it reintroduces a proven bug); (2) the VH-07 P3 rule (non-address Unbounds stop vetoing + its 3 pins — orthogonal, owns the only 7 measured conversions). Update CONTEXT.md glossary + AGENTS.md validation state + record the decision (ADR or validation-state note); the affine-equalities/var-bounds/vla-handling specs stay as history, marked superseded.

**Done when:** `git diff 344d825...HEAD` shows only the two kept hunks plus docs; full battery green (unit suite, corpus 32/32 + IR-identity vs 344d825 control save the known AE frame fold, allocas, 8/8, both 30/2 gates, coreutils); suite count and numbers rewritten with fresh timestamps.
