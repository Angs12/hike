# Affine relations: precision vs cost ledgers

Scope: `var-bounds` @ f4683a2, `vla-handling` @ a338f45, baseline 344d825. No builds run; behavior claims cite AGENTS.md batteries and ticket messages. No recommendation.

## 1. Precision ledger

| Claim | Source |
|---|---|
| F1-NEQ needs no affine: pre-exists on 344d825 (`test_properties.ml:801`), reads `AI.find_word` word sets, fires via landmark Finite extrapolation (6dd9cce). Affine concedes the shape — AE-S1 joins step-2 counters densely. | 344d825 tree; `test_affine.ml:91-99` |
| Zero corpus tags from equalities: 2597 Range tags, 0 var floors; alloca_vla identical both trees (39xRange(-64,268), 19xUnbounded); 32/32 IR-identical vs ec8c17d. | AGENTS.md VB-06 table |
| Verdict fires nowhere real: alloca_vla sizes go through align masks/libcall (V19-style miss) and loop-indexed dynamics (V20-style miss). | e4492d2 msg |
| Solver never decides on corpus: 0 floors so all-const folds equal the old hull; ALL-sub dumps 32/32 identical vs cf7ece4. Sole solver-touched delta: 5 VLA-touching coreutils DIFFERs, same stack_r counts, behavior-neutral. | e4492d2 msg; AGENTS.md VB-06 coreutils rows |
| VH-01 spill rule: 0/8 floors, tags identical 32/32 vs 51be2c9 (spills keep the +1 root the verdict rejects). VH-02 bounds arms: no-op, dumps identical 32/32 mains + ALL-sub on 4 loop binaries. | 8e19400, 9ad2647 msgs |
| All affine precision is fixture-level: verdict V13-V25b/V28/V29, merge C4c/R11b/C4d/R11c/VB-M3..M8, plan S8/VB-F1/F2, solver VB-S, mirror VH1/VH02-M — hand-built bounds, none fed by a production fixpoint. | `test_vla.ml`, `test_var_bounds.ml:117-166` |

## 2. Cost ledger

| Claim | Source |
|---|---|
| Wall-time +3.7% (975.2s vs 940.4s /104 lifts, solver cost); earlier +4.6% (1492.0s vs 1427.3s, join/query cost). | AGENTS.md VB-06 + AE rows |
| Diff vs 344d825: +4164/-258, 30 files. New: `cbat_affine` 577+126, `cbat_var_order` 152+22; `cbat_vsa.ml` +500/-49; `hike_stack_model.ml` +314/-105; tests +1749 lines. | `git diff 344d825..a338f45 --stat` |
| Suite 566 -> 610 (VB-M4..M8 pins) -> 615 (VH-07) -> 637 (VH-02 +25); green throughout, 6 xfail. | aa8060b, 11758da, 974764b, 9ad2647 |
| No production regression: dark-then-lit landing (VB-01 dark, VB-03/04 light-up, VB-05 deletion) kept every battery green. Debt: stale solver comment (fc9a83d), dead bil2llvm VLA arm (a50a044 S2/P5), pre-existing stale frame-fvar read on VLA align-down chain (VH-02 msg). | ticket msgs |

## 3. Large-region alternative (split-plan vocabulary)

| Claim | Source |
|---|---|
| Means one extent-overlapping region, `convertible=false` (alloca_vla today: single -r0 (-64,268), 39 members). Rule exists: `convertible` needs const bounds; `is_abi_visible` false on Var floors; `region_bytes` saturates astronomic spans into the size-guard reject. | `hike_stack_model.ml:464-500,536-640` |
| Unchanged: per-region `frame_escapes` veto, outgoing-tail veto, `has_unbounded_access` plan veto, `tags_inside_or_disjoint`, write-closed may-overlap merge. | `hike_stack_model.ml:700-900` |
| alloca_vla converts nothing either way (0 stack_r regions both trees). VH-00 forced-no-hull: even 7 live floors + 6 convertible const regions give plan [] (`tags_inside_or_disjoint=false`; P0 escape binds independently). | `docs/vh00-isolation-experiment.md`; `/home/tovpr/backup/vh00-dumps/` |
| Loss vs today: zero measured corpus conversions. Fixture-level loss: S8 + VB-F1/F2, C4d/R11c, VB-M3..M8. VH-07's 7 newly-converting subs come from the orthogonal P3 rule (non-address Unbounds) and survive either VLA treatment. | AGENTS.md VB-06; 974764b |

## 4. Revert shapes

| Option | Files | Gates | Sacrificed |
|---|---|---|---|
| (a) Full revert to 344d825 | Delete `cbat_affine.*`, `cbat_var_order.*`, `test_affine/test_var_bounds/test_vla.ml`; revert `cbat_vsa.ml`, `cbat_ai_representation.*`, `convutils.ml`, `hike_stack_model.ml`, `hike_vsa.ml`, `hike.mli`, `bil2llvm.ml`, `test_regression.ml`, probes | Full battery: unit, corpus 32/32 + IR-identity (expect alloca_vla frame 336B->128B per AE battery), allocas 160, semantics 30/2, opt 30/2, 8/8, coreutils 104/108 | ~1700 fixture pins (V13-V29, C4c/R11b/C4d/R11c, VB-M/F, VB-S, AE-E/R/S, VH rows). F1-NEQ survives. IR predicted identical save the AE frame fold |
| (b) Revert floor/solver only, keep equalities | Delete `cbat_var_order.*`, `test_var_bounds/test_vla.ml`; revert bound generalization, VH-06 bypass, solver call + may-subset merge, verdict. Keep `cbat_affine.*` + mirror + `test_affine.ml` | Same battery | Same production IR as (a) (floors never fire). Kept AE-E/R/S pins buy no recorded production tag (VH-01 0/8, VH-02 no-op) |
| (c) Keep all, climb ladder | Forward only: escape lane (VH-03), guard-cap feeder + loop-bound reasoning (ADR-0007 out-of-scope), %e4f fork (VH-00 P4) | Same battery per change | Nothing; open ladder with 0 floors firing to date |
