# Landmark-Directed Widening — Spec

**Status:** ready-for-agent
**Feature:** landmark-directed-widening
**Base branch:** `recover-golden` (restored from `stash@{0}`; holds AGENTS.md landmark claims, 279 baselines incl. 93 coreutils, 10 green-gate issues, threshold-based VSA)
**Design inputs:** `AGENTS.md` §Widening (lines ~214-237), `.slim/deepwork/not-yet-landed.md` (Landmarks+int64), `docs/adr/0002-two-phase-vsa-for-arity.md`, recovered pi session `01a03eb4` (2026-08-26) edit patches + reads.
**Reference paper:** Simon & King, *Widening Polyhedra with Landmarks*, APLAS 2006.

## Problem Statement

The hike VSA is *documented* as using landmark-directed widening — a faithful port of Simon & King — and a working state once passed 93 coreutils with all gates green and carried FP use/semantics. But the landmark *runtime* was never committed: the live code uses threshold-based widening (`cbat_thresholds`, "per-sub threshold ladders"), the landmark unit tests in `test_cbat.ml` are stubbed ("not yet enabled"), and the FP semantics live only in an uncommitted session. We recovered the documented/baseline golden state to `recover-golden`, yet it still lacks the actual landmark-directed widening and the wired FP semantics. The user wants the VSA to *genuinely* use landmarks (as AGENTS.md claims), with 93 coreutils passing, all gates green, and FP use/semantics present — i.e. the true golden state, durably in the repo rather than trapped in a session transcript.

## Solution

Implement landmark-directed widening per the Simon & King port described in `AGENTS.md` / `not-yet-landed.md`: recreate the dedicated `cbat_landmarks.ml` module (recovered from pi session `01a03eb4`, fixing its compile error), wire **acquisition** (`observe_unsat` in `meet_var` when a guard meets a value set empty) and **consumption** (`lm_calc_steps` → `selective_widen_extrapolate` at WTO heads) into the fixpoint, replace the threshold ladder with landmark extrapolation, and restore FP use/semantics in the `bil2llvm` emission layer, targeting the corrected (width-homogeneous) BAP FP modeling (AGENTS.md §X1-c / BUG C). Then unstub the Lane Z v2 tests, re-run the coreutils pipeline to confirm 93/93, and close the green-gate issues — so the code finally matches the docs.

## User Stories

1. As a VSA author, I want `meet_var` to record a landmark when a guard constraint meets a var's value set empty, so that disabled behaviors become landmarks of the enclosing WTO cycle.
2. As a VSA author, I want each WTO SCC member attributed to its innermost cycle head, so that observations are recorded only for widening-cycle vars.
3. As a VSA author, I want the climb/closure rate computed from two consecutive distance measurements at a cycle head, so consumption can extrapolate in one pass.
4. As a VSA author, I want the widening point to extrapolate by the estimated remaining traversals (`floor(dcur/(dprev-dcur))`) instead of dropping unstable bounds, so it reaches the least fixpoint in one pass.
5. As a VSA author, I want landmark distances capped at 2^40, so extrapolation never runs away.
6. As a VSA author, I want memory cells to carry no landmarks, so the memory abstraction stays independent of the landmark machinery.
7. As a VSA author, I want `current_lm_head` bound around the deferred block-transfer closure so `observe_unsat` reads the correct head, so acquisition attributes landmarks to the right cycle.
8. As a VSA author, I want a `landmark_env` holding the head→landmark-list table, so acquisition and consumption share state across the fixpoint.
9. As a VSA author, I want `Clp.widen_join` (Listing 4) to translate an unstable bound by the observed growth · steps, rounded outward onto the join's progression grid, so the CLP domain extrapolates consistently with the polyhedra paper.
10. As a VSA author, I want a translation escaping the word to take the infinite (∞-steps) arm, so soundness is preserved at overflow.
11. As a VSA author, I want `selective_widen_extrapolate` in the AI representation to apply landmark consumption only to per-head value-flow cycle vars, so selective widen and landmark consume compose.
12. As a VSA author, I want the threshold ladder (`cbat_thresholds`) removed entirely, so landmark-directed widening is the sole extrapolation (matching the ADR's "thresholds were deleted").
13. As a VSA author, I want the `cbat_landmarks.ml` module to compile cleanly (fixing the pi-session compile error at line 131), so the landmark machinery builds.
14. As a VSA author, I want landmark acquisition/consumption to be a no-op outside any WTO cycle (vars with no head), so non-looping code is unaffected.
15. As an analyst, I want the guarded counter loop (K=100) to stabilize its head state at exactly K+1 = 101 (the true least fixpoint) rather than widening to a geometric rung like 127, so precision matches the paper's property LM F1.
16. As an analyst, I want the guard-continue (taken) view bounded by K exactly, so the honest `<= K` property is asserted on the correct edge.
17. As an emitter author, I want FP intrinsics (mulsd/addsd/divsd/subsd/cvtsi2sd/cvttsd2si, and the cast/convert classes `cast_sfloat_*`/`cast_float_*`/`cast_sint_*`/`fconvert_*`) modeled as CALLS to `intrinsic:*` subs whose bodies are bit-precise IEEE-754 soft-float BIL, so FP *use* is present — including the body-less cast/convert stubs BAP does not auto-expand (classified via `mapped_fp_intrinsic`, not body presence).
18. As an emitter author, I want FP semantics (rounding, NaN/order/convert) to be bit-precise soft-float and **width-homogeneous** — each SSE result width threads its own phi/lane (no name-only lane conflation) — so lifted doubles are exact (e.g. `div.c` nc=128.75, printf boundary 3.0) and behave like native.
19. As a tester, I want the Lane Z v2 ("Widening Polyhedra with Landmarks") tests in `test_cbat.ml` unstubbed and actually exercising acquisition + consumption end-to-end, so regressions in landmark widening are caught.
20. As a tester, I want property LM F1/F2a (counter loop finite fixpoint, widen_join soundness) to be real checks, not `(stub)` placeholders, so soundness is enforced.
21. As a release engineer, I want `scripts/coreutils_pipeline.sh` to report 93/93 coreutils success (native-vs-lifted), so the golden corpus rate is reproducible.
22. As a release engineer, I want `dune build` and the green-gate issue checks (`.scratch/gate-green-context/issues/*`) to pass, so "all gates pass" is machine-verifiable.
23. As a maintainer, I want AGENTS.md's claim ("Widening is LANDMARK-DIRECTED… landed 2026-08-23") to be true of the code, or corrected, so docs and implementation never diverge.
24. As a maintainer, I want the recovered implementation captured from pi session `01a03eb4` to be committed (not left in a transcript), so the work survives session loss.
25. As a reviewer, I want landmark changes covered by external-behavior tests (loop bounds, fixpoint value) rather than implementation-detail assertions, so the tests don't churn with refactors.
26. As a user, I want the analysis to remain sound (no unsound over-approximation) when landmarks are present, so enabling them never breaks correctness.
27. As an onboarding engineer, I want a short ADR/README note mapping the Simon & King listings (1-4) to the modules/functions that implement them, so the port is navigable.
28. As an emitter author, I want every SSE interface temp canonicalized to its width-suffixed name (the BAP `sse-binary` result-width suffix, e.g. `fadd_rne_ieee754_binary_32` vs `_64`), so hike's maps never collapse same-name diff-width lanes (the BUG C root cause).
29. As an emitter author, I want `rename_intrinsics` to canonicalize interface temps to width-suffixed names and `create_native_fp_call` to resolve x-operands from the most-recent in-block `intrinsic:xN_*` def and bind every consumer-width view (y0_64/y0_32/y0_1), so no lookup conflates lanes and all consumers read the right width.
30. As an emitter author, I want the installed semantics table (`x86-64-sse-intrinsics.lisp`) to contain COMISS/COMISD entries (rm/rr) with UC-identical BIL, so conditional branches consume correct FP flags instead of stale integer flags.
31. As a VSA author, I want the VSA's abstract FP/value modeling to stay width-aware (not assume name-only identity) so it composes with the corrected BAP FP lanes.
32. As a maintainer, I want BUG B (poison reaching live soft-float input params via `get_local None`) tracked as a known-open issue with a regression probe, so it is not silently regressed while landmark work proceeds.
33. As a tester, I want a FP regression probe (e.g. `div.c` exact double, a COMISS-guarded branch) in the corpus/semantic harness, so the corrected FP modeling stays green.

## Implementation Decisions

- **New module `cbat_landmarks.ml`** (recreated from pi session `01a03eb4`): holds `landmark_env : ((Tid.t, Tid.t) Hashtbl.t * (TidVar.t, landmark list) Hashtbl.t) option ref`, `current_lm_head : Tid.t option ref`, `heads_of_wto`, and the acquisition/consumption helpers (`observe_unsat`, `lm_calc_steps`). Must compile — the recovered version had a compile error at line 131 to fix (likely a signature/record-field mismatch against the current `cbat_vsa` types).
- **`cbat_vsa.ml` (fixpoint):** add the `landmark_env`/`current_lm_head` refs; modify `meet_var` to call `observe_unsat` on an empty meet (acquisition), attributing the excluded boundary + distance to the innermost WTO head of `current_lm_head`; modify the widening point (currently `label_widening_points` / `selective_widen_join_threshold`) to consume landmarks via `lm_calc_steps` → `selective_widen_extrapolate`. Keep `current_lm_head` bound around `denote_block_with_stores`.
- **`cbat_clp.ml` (CLP domain):** `widen_join` becomes the Listing-4 extrapolation — stable bounds kept, unstable bounds translated by (growth · steps), rounded outward onto the join's progression grid; translation escaping the word takes the ∞-steps arm. (`Clp.extrapolate_steps` from the old API is consolidated into `widen_join`, matching the existing test shims.)
- **`cbat_ai_representation.ml`:** `selective_widen_extrapolate ~need ~reach_mem ~steps` applies landmark consumption only to per-head value-flow cycle vars (SiftAbs H3 selective-widen composition).
- **`bil2llvm.ml` (emission) — target the CORRECTED BAP FP modeling (changed 2026-08-25, AGENTS.md §X1-c / BUG C):** BAP's `sse-binary` now appends the result width to the intrinsic name (`fadd_rne_ieee754_binary_32` vs `_64`), so addss/addsd map to distinct width-homogeneous subs; `native_fp_op` maps both suffixed and legacy names. Restore FP *use* (`fp_intrinsic` class + the body-less cast/convert classes, classified via `mapped_fp_intrinsic`) and FP *semantics* (bit-precise IEEE-754 soft-float BIL bodies, COMISS/COMISD table entries). Implement `rename_intrinsics` width-suffix canonicalization and `create_native_fp_call` binding every consumer-width view (y0_64/y0_32/y0_1) from the most-recent in-block `intrinsic:xN_*` def. If replaying the pi-session (`01a03eb4`) `bil2llvm.ml` patches, verify they match this post-fix modeling — not the pre-fix width-blind version.
- **No threshold fallback — landmark-directed widening is the sole extrapolation.** Per `AGENTS.md`/`not-yet-landed.md` the threshold ladder was "deleted" in the landmark era, but `cbat_thresholds.ml` is still present and active in `recover-golden`. Decision: **delete `cbat_thresholds.ml` and all `selective_widen_join_threshold` call sites**; `widen_join` / `selective_widen_extrapolate` (landmark) become the only widening path. There is no toggle back to thresholds. If the recovered pi-session implementation cannot be retrieved (see Further Notes), landmarks are **re-implemented from the design docs + paper**, never by re-enabling thresholds.
- **Soundness invariant:** memory cells carry no landmarks; acquisition/consumption are no-ops outside WTO cycles; distances cap at 2^40.
- **No new public API churn:** the existing `Clp.widen_join` / `AI.selective_widen_*` names are preserved (the test shims in `test_cbat.ml` already expect `AI.selective_widen_extrapolate` and `Clp.widen_join`), so the unit tests wire in directly once unstubbed.
- **No file-path or code-snippet commitments here** — module names above are the seams; exact function signatures are decided during implementation against the current `cbat_vsa` types.

## Testing Decisions

- **Test external behavior, not implementation detail.** Landmark tests assert loop head-state bounds, fixpoint values, and `widen_join` soundness (join ⊆ result) — never internal table contents.
- **Seams (highest, fewest):**
  1. `test_cbat/test_cbat.ml` — unstub the Lane Z v2 / "Widening Polyhedra with Landmarks" block (currently `(stub)`, "not yet enabled"): make property LM F1 (counter loop finite fixpoint = K+1), F2a (widen_join soundness), and the `lm_jle_loop` acquisition/consumption end-to-end checks real.
  2. `scripts/coreutils_pipeline.sh` — the 93-coreutils native-vs-lifted success-rate gate; target 93/93.
  3. `dune build` + `.scratch/gate-green-context/issues/*` green-gate checks — the "all gates pass" gate.
- **Prior art:** the existing Lane Z v2 scaffolding and `lm_*` helpers in `test_cbat.ml`; `scripts/run_corpus.sh` (31/31 rc=0 baseline); `scripts/coreutils_pipeline.sh` resumable pipeline; the 10 green-gate issue checklists.
- **FP regression probe:** `div.c` prints exact double (`nc=128.750000`), a `COMISS`/`COMISD`-guarded branch takes the correct path, and no same-name diff-width lane conflation occurs (doubles exact at the printf boundary 3.0). Re-run `run_semantic_all.sh` (31/31) and `check_allocas.sh` (124/0) as the FP gate.
- **Regression guard:** since there is no threshold path, regression coverage targets only the landmark path (acquisition + consumption + `widen_join` soundness). Any re-introduction of a threshold ladder would be a new feature, not a fallback.

## Out of Scope

- Threshold-based widening entirely (removed — no fallback retained; landmark-directed is the sole extrapolation).
- The two-phase VSA-for-arity machinery (ADR 0002) except where it intersects the widening point.
- Stage-timer / performance instrumentation (ADR 0003) beyond not breaking it.
- New benchmark corpora beyond coreutils; new ADRs unless a decision can't be expressed in prose.
- Re-implementing the Simon & King paper from scratch — we port the recovered `01a03eb4` implementation, fixing its compile error.

## Further Notes

- **Source of truth for the lost implementation:** pi session `01a03eb4` (2026-08-26). Its `edit` toolResults carry unified `patch` diffs and `read` toolResults carry file chunks (incl. `cbat_landmarks.ml` at the failing line 131, `landmark_env`/`observe_unsat`/`heads_of_wto` in `cbat_vsa.ml`, landmark edits in `cbat_clp.ml`/`cbat_ai_representation.ml`, and FP edits in `bil2llvm.ml`). Recover by replaying those patches onto `recover-golden`, not by hand-rewriting. **If retrieval is not possible** (patches fail to apply, or do not compile even after fixing line 131), then **re-implement** landmark-directed widening from `AGENTS.md` §Widening, `.slim/deepwork/not-yet-landed.md`, ADR 0002, and the Simon & King paper — do **not** fall back to or re-enable `cbat_thresholds`.
- **BAP FP modeling changed (2026-08-25):** the SSE intrinsic naming now carries result width (`fadd_rne_ieee754_binary_32`/`_64`), and hike must canonicalize interface temps to width-suffixed names (`rename_intrinsics`) and bind all consumer-width views. The landmark/VSA work must not regress this: FP lanes stay width-homogeneous, COMISS/COMISD are present, and **BUG B (poison to live soft-float input params) remains OPEN** and is tracked as a known issue (user story 32).
- **Working base:** branch `recover-golden` (created during recovery) already has AGENTS.md landmark claims, 279 baselines (93 coreutils), `scripts/coreutils_pipeline.sh`, and the 10 green-gate issues. Implement on top of it.
- **`m2` and `stash@{0}` are preserved** as fallbacks; the landing branch for this work should be `landmark-directed-widening` off `recover-golden`.
- **Docs/code divergence risk:** AGENTS.md states landmark widening "landed 2026-08-23"; once implemented, either the code matches (ideal) or AGENTS.md is corrected. Do not leave them contradictory.
- **Split into tickets** via `/to-tickets` after this spec is accepted; each ticket should declare its blocking edges (e.g., `cbat_landmarks.ml` compiles before `cbat_vsa.ml` wires acquisition; FP emission independent of widening).

