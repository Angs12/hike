# Landmark-Directed Widening — Spec v2

**Status:** ready-for-agent
**Feature:** landmark-directed-widening
**Base branch:** `landmark-directed-widening` (off `230b6c4 wip: relevance closure fix + memside-effect propagation + §8 BIL-no-pattern-match partial`)
**Design inputs:** `AGENTS.md` §Widening (lines ~214–237), `AGENTS.md` §8 (BIL-no-pattern-match, `Targetutils.sp`, 100% VSA-tagging invariant), `.scratch/landmark-directed-widening/spec.md` (the v1 design — superseded by this v2 for the §8 + 230b6c4-era constraints), the original Simon & King APLAS 2006 paper.
**Reference paper:** Simon & King, *Widening Polyhedra with Landmarks*, APLAS 2006.
**Prior spec:** `.scratch/landmark-directed-widening/spec.md` (v1) — read for the original design rationale; this v2 supersedes it for the §8-era implementation and the 230b6c4 baseline.

---

## Problem Statement

The hike VSA is *documented* (AGENTS.md §Widening) as using landmark-directed widening — a faithful port of Simon & King, APLAS 2006 — and the live code is supposed to use landmark extrapolation as its sole extrapolation. The *actual* production code at `230b6c4` does not:

- The active widening is `Cbat_ai_representation.selective_widen_join_threshold` (line 281), which dispatches to a **threshold ladder** (`Cbat_thresholds`, `Clp.widen_join_threshold` with a hemisphere gate) — the Astrée-style bounded-extrapolation against `geometric 8*2^k` rungs.
- `Cbat_landmarks` is a 37-line stub (line 36: `lm_calc_steps _ = \`Inf`); it is **not in `dune`**, **not imported by any source**, and its `observe_unsat _ _ = ()` is a no-op.
- The unit tests at `test_cbat.ml:7813–7827` (the F2a / F2b / F2c checks) are explicit `(stub)` placeholders that assert `true` and admit "extrapolate_steps API was consolidated into widen_join" without it being consolidated.
- AGENTS.md's table says 3 unit failures (LM F1 + LM F2c × 2) — those are the *target* failures this workstream must turn green, and the gap between docs and code is the central problem.

The VSA's precision loss on guard-bounded counter loops is the visible symptom. With K = 100, the threshold ladder pins the head bound to the *rung just above K* (127 in the current geometric family `8*2^k`); the true least fixpoint is K + 1 = 101. Landmarks, by construction, extrapolate to the *first iterate at which a disabled behavior becomes enabled* — i.e. exactly K + 1.

The user wants the VSA to *genuinely* use landmarks (as AGENTS.md claims), with the threshold ladder **deleted entirely** (no fallback), the unit tests **real** (not stubs), the corpus emission staying at 31/31 rc=0, the structural asserts holding at 124/0, and the semantic gate **no worse than the 28/3 baseline** (the Q4 refinement: no new regressions, not absolute green — three semantic regressions — `out_nested_struct`, `out_va_arg_vacopy`, `out_variadic` — are pre-existing and tracked separately under `.scratch/one-frame-anchor-removal/`).

---

## Solution

Implement faithful landmark-directed widening per Listings 1–4 of Simon & King, APLAS 2006:

1. **Acquisition** (paper Listing 1, `updateLandmark`): on every meet that produces Bottom, record a landmark per violated bound, attributed to the enclosing WTO cycle head.
2. **Advance** (paper Listing 2, `advanceLandmarks`): at each widening-point visit, commit the current distance as the previous distance, reset the new previous to ∞.
3. **Step calculation** (paper Listing 3, `calcIterations`): `steps ← 0` if any landmark has `dist_p = ∞`; `steps ← ∞` if no landmark has two measurements; else `steps ← min over landmarks(dist_c / (dist_p − dist_c))`.
4. **Extrapolation** (paper Listing 4, `extrapolate`): for each non-redundant bound `e ≤ c` of `P1`, compute `c' = min(P1 ⊔ P2, e)`. If `c' ≤ c`, keep; if `steps = ∞`, drop (plain widening); else translate to `c + (c' − c) · steps`, rounded outward onto the word grid; if translation escapes the word, take the ∞-arm for that bound.

Then **delete the threshold ladder** (`cbat_thresholds.ml`, all `*_widen_join_threshold` exports, the `selective_widen_join_threshold` call site at `cbat_vsa.ml:2789`). Landmark extrapolation becomes the sole extrapolation path. The `Clp.widen_join` function becomes the standard Cousot-Halbwachs widening (no threshold, no landmark — the ∞-arm); `Clp.extrapolate_steps` becomes the listing-4 extrapolation with a finite `steps` argument. The production fixpoint calls `AI.selective_widen_extrapolate ~need ~steps`, which dispatches per var in `need` to the word lane (which calls `Clp.extrapolate_steps` when `steps` is finite, `Clp.widen_join` when `steps = ∞`) and per memory cell to the plain `Mem.widen_join` (memory carries no landmarks — Q5).

**New 1000-iteration corpus binary** (`src/progs/landmark_loop_1000.c`): a counter loop bounded at exactly K = 1000, compiled as PIE per `compile_corpus.sh`. Its purpose: a *large-K* witness for the K = 100 unit test. The threshold ladder's geometric family `8*2^k` has a rung at 1024 (close to 1000), so the pre-landmark fixpoint overshoots by 24 (1024 − 1000). With landmarks, the fixpoint converges at exactly 1001. This binary is the regression oracle for the production widening path — if the lifted LLVM IR's `i` value is bounded at 1001 in the head-state, landmarks are working; if it's bounded at 1023 or 1024 or higher, the threshold ladder is leaking.

The acquisition path must respect AGENTS.md §8: **no AST pattern matching on BIL constructors** (use `Exp.visitor` / `Term.visitor` exclusively), **no hardcoded `"RSP"`/`"RBP"`** (use `Targetutils.sp`), and the **100% VSA-tagging invariant** must hold (every `stack_access`-tagged def has a `vsa_info` tag). In practice this means the acquisition seam at `meet_var` queries the `WordSet` for violated bounds via its existing abstract API — it does not inspect the *guard* expression's BIL shape.

The consumption path (T07b `Clp.extrapolate_steps`) operates on `Clp.t` — an abstract lattice value, not a BIL exp — and is §8-clean by construction.

---

## User Stories

### Acquisition (the paper's Listing 1)

1. As a VSA author, I want `meet_var` to record a landmark when a guard constraint meets a var's value set empty, so that disabled behaviors become landmarks of the enclosing WTO cycle.
2. As a VSA author, I want the recorded landmark to be a triple `(inequality, dist_c, dist_p)` per paper §4, so consumption has the climb/closure rate.
3. As a VSA author, I want each WTO SCC member attributed to its innermost cycle head, so observations are recorded only for widening-cycle vars.
4. As a VSA author, I want `current_lm_head` bound around the deferred block-transfer closure, so `observe_unsat` reads the correct head.
5. As a VSA author, I want a `landmark_env` holding the head → landmark-list table, so acquisition and consumption share state across the fixpoint.
6. As a VSA author, I want acquisition to be a no-op outside any WTO cycle (vars with no head), so non-looping code is unaffected.
7. As a VSA author, I want acquisition to fire **per violated bound** (not per meet — Q7), so multiple disabled behaviors at one meet each contribute a landmark.
8. As a VSA author, I want acquisition to query the `WordSet` for violated bounds (not inspect BIL shapes — §8), so the acquisition path is §8-compliant.
9. As a VSA author, I want the same (violated) bound in two consecutive meets to be deduplicated per `updateLandmark`'s rule (smaller distance wins; second measurement upgrades `dist_p` from ∞ to the new `dist_c`), so the table converges to one entry per inequality per head.

### Consumption (the paper's Listings 2–4)

10. As a VSA author, I want the climb/closure rate computed from two consecutive distance measurements at a cycle head, so consumption can extrapolate in one pass.
11. As a VSA author, I want the widening point to extrapolate by the estimated remaining traversals (`floor(dist_c / (dist_p − dist_c))`) instead of dropping unstable bounds, so it reaches the least fixpoint in one pass.
12. As a VSA author, I want `Clp.extrapolate_steps : steps:int -> t -> t -> t` (paper Listing 4): stable bounds kept (`c' ≤ c` ⇒ keep `e ≤ c`); unstable bounds translated by `(c' − c) · steps`; ∞-arm if `steps = ∞`; rounds outward onto the word grid; translation escaping the word takes the ∞-arm for that bound.
13. As a VSA author, I want `Clp.widen_join : t -> t -> t` to remain the standard Cousot-Halbwachs widening (no threshold, no landmark — the ∞-arm), so existing call sites that want plain widening still work.
14. As a VSA author, I want the two entry points (`Clp.widen_join` plain, `Clp.extrapolate_steps` finite-steps) to share the same lattice interface, so the lattice signature stays 2-arg.
15. As a VSA author, I want `AI.selective_widen_extrapolate : need:Var.Set.t -> reach_mem:bool -> steps:int -> t -> t -> t` to apply landmark consumption only to per-head value-flow cycle vars (the `need` set — Q3), so selective widen and landmark consume compose.
16. As a VSA author, I want memory cells to carry no landmarks — `Mem.widen_join` is called plain for memory cells regardless of `steps` (Q5) — so the memory abstraction stays independent of the landmark machinery.
17. As a VSA author, I want landmark distances capped at 2^40, so extrapolation never runs away.
18. As a VSA author, I want a translation escaping the word to take the infinite (∞-steps) arm, so soundness is preserved at overflow.
19. As a VSA author, I want landmark acquisition/consumption to be no-ops outside any WTO cycle (vars with no head), so non-looping code is unaffected.

### Cleanup

20. As a VSA author, I want the landmark table cleared at consumption for the head `H` AND all strict descendants of `H` in the WTO tree (Q9), so stale inner-cycle landmarks don't poison outer-level consumption.
21. As a VSA author, I want `lm_advance` (Listing 2) called at the start of each head widening visit, so the second-measurement is committed before `lm_calc_steps` reads it.

### The threshold ladder deletion

22. As a VSA author, I want the threshold ladder (`cbat_thresholds.ml`) removed entirely, so landmark-directed widening is the sole extrapolation (matching the spec's "no fallback" doctrine).
23. As a VSA author, I want every `selective_widen_join_threshold` call site removed, so the threshold path is unreachable in source.
24. As a VSA author, I want every `*_widen_join_threshold` export removed from `*.mli` files, so the public API does not advertise the deleted path.
25. As a VSA author, I want the `dune` entry for `cbat_thresholds` removed, so the module cannot be reintroduced accidentally.
26. As a maintainer, I want `grep -r 'threshold' src/cbat_vsa/` to return 0 matches at the end of Stage 3, so the deletion is provably complete.

### The 1000-iteration corpus binary

27. As an analyst, I want a new corpus binary `landmark_loop_1000` in `/tmp/corpus/` (built from `src/progs/landmark_loop_1000.c` by `scripts/compile_corpus.sh`), so I have a real-binary witness for the K = 100 unit test.
28. As an analyst, I want the binary to be a PIE-only `gcc -O0 -fno-stack-protector` build (per the compile_corpus.sh recipe), so it matches the rest of the corpus.
29. As an analyst, I want the binary's lifted LLVM IR to bound the loop counter `i` at exactly 1001 in the head-state (the true least fixpoint — the value 1000 is the loop bound, the head-state has i ranging over [0..1000]), so I have an external-behavior oracle for landmark convergence.
30. As an analyst, I want the binary to print the loop counter on exit (e.g. `printf("%d\n", i)`), so the semantic harness can verify the lifted binary executes correctly and the VSA's i-bound is consistent with the runtime behavior.
31. As an analyst, I want the binary to be added to the `check_allocas.sh` structural-assert pipeline (a stack access exists, allocas are produced), so any widening change that breaks the IR is caught.
32. As an analyst, I want the binary to be added to `run_semantic_all.sh` and pass (native-vs-lifted byte-diff), so the landmark path is validated end-to-end on a real binary.
33. As a tester, I want the binary's fixpoint to be re-checked by `cbat_ai_representation.extrapolate_steps` directly (a unit test on the lifted `i` bound at the head tid), so the production path has a unit-testable oracle.

### Unstubbing the lane Z tests

34. As a tester, I want the Lane Z v2 ("Widening Polyhedra with Landmarks") tests in `test_cbat.ml` unstubbed and actually exercising acquisition + consumption end-to-end, so regressions in landmark widening are caught.
35. As a tester, I want property LM F1 (counter loop `i = 0; while i < 100 do i++ done` produces a fixpoint at exactly `i = 100` in `Q.head`) to be a real check, not a `(stub)` placeholder.
36. As a tester, I want property LM F2a (`Clp.widen_join` soundness: `p1 ⊑ p1 ∇ p2` and `p2 ⊑ p1 ∇ p2`) to be real, not stubbed.
37. As a tester, I want property LM F2c (two-loop `lm_jle_loop ~k1:(w32 40) ~k2:(w32 100)` stabilizes at exactly K1+1 = 41 and K2+1 = 101) to be real, not stubbed.
38. As a tester, I want a new property LM F1-acquire (the `lm_jle_loop` end-to-end: the fixpoint records at least one landmark with `dist_p` finite and `dist_c < dist_p`) to be a real check.

### Validation contract

39. As a release engineer, I want `dune runtest` to report 0 FAIL at the end of Stage 3, so the LM unit tests pass.
40. As a release engineer, I want `run_corpus.sh` to report 31/31 rc=0 at the end of Stage 3 (now 32/32 if the new binary is included), so the corpus emission holds.
41. As a release engineer, I want `check_allocas.sh` to report 124/0 (or 125/0 with the new binary) at the end of Stage 3, so the structural asserts hold.
42. As a release engineer, I want `run_semantic_all.sh` to report no fewer than 28/3 PASS at the end of Stage 3 (i.e. not regress the pre-existing 3 failures and not introduce new ones), so the Q4 contract holds.
43. As a release engineer, I want `run_semantic.sh` (8-bin) to report 8/8 PASS, so the canonical oracle holds.
44. As a maintainer, I want AGENTS.md's claim ("Widening is LANDMARK-DIRECTED… landed 2026-08-23") to be true of the code at the end of Stage 3, so docs and implementation never diverge.

### Documentation + ADRs

45. As an onboarding engineer, I want a short ADR (`docs/adr/0002-landmark-directed-widening.md`) mapping the Simon & King listings (1-4) to the modules/functions that implement them, so the port is navigable.
46. As an onboarding engineer, I want `CONTEXT.md` updated with the new vocabulary terms (Landmark, Landmark Acquisition, Landmark Consumption, Widening Point, Standard Widening, Extrapolation) and the deleted-terms list (no more "threshold ladder", "rung", "hemisphere gate", "strict-rung rule"), so the glossary is current.
47. As a maintainer, I want AGENTS.md §Widening (lines ~214–237) rewritten to describe the actual code at Stage 3, not the v1 spec.

### Out-of-scope reminders

48. As a maintainer, I want the FP intrinsics (issues 10–13 in the v1 spec) to remain out of scope (already landed at 2026-08-25 per the validation table).
49. As a maintainer, I want the 3 pre-existing semantic regressions (`out_nested_struct`, `out_va_arg_vacopy`, `out_variadic`) to remain out of scope (tracked under `.scratch/one-frame-anchor-removal/`).
50. As a maintainer, I want the `mem_access_via_ptr` §8 violation in `src/bil2llvm.ml:196–206` to remain out of scope (flagged in the 230b6c4 commit message).

---

## Implementation Decisions

### Three-stage landing (per the design tree)

The implementation is **three PRs, each gates-green**, landing in this order:

- **Stage 1 (API split, pure refactor)**: `Clp.widen_join` becomes the plain Cousot-Halbwachs widening (no threshold, no landmark); `Clp.extrapolate_steps` is added as a new 2-arg entry point implementing Listing 4. Nothing is *called* yet. The threshold widening path is still the production path.
- **Stage 2 (acquisition + consumption built but not consulted)**: full landmark machinery runs in parallel. The fixpoint still calls the threshold widening. Landmarks are recorded (silently) and `lm_calc_steps` runs (silently).
- **Stage 3 (switch, delete, unstub, document)**: the production fixpoint calls `selective_widen_extrapolate`; the threshold ladder is deleted entirely; the unit tests are unstubbed; AGENTS.md / CONTEXT.md / ADR are updated.

### Module structure

- **`cbat_landmarks.ml`** (rewrite): the new module — `landmark_env : (Tid.t, (Var.t * inequality * dist_c * dist_p) list) Hashtbl.t ref`, `current_lm_head : Tid.t option ref`, `heads_of_wto`, `clear : head:Tid.t -> unit` (clears `H` + strict descendants — Q9), `observe_unsat : p:WordSet.t -> cstr:WordSet.t -> unit` (per violated bound, queries WordSet — §8), `lm_advance : head:Tid.t -> unit` (Listing 2), `lm_calc_steps : head:Tid.t -> [> \`Zero | \`Finite of int | \`Inf]` (Listing 3). Added to `dune`'s `cbat_vsa_domain` modules.
- **`cbat_clp.ml`** (extend): `widen_join` becomes the plain Cousot-Halbwachs widening (drops unstable bounds, no threshold); `extrapolate_steps ~steps p1 p2` is added (Listing 4). Both share the lattice interface.
- **`cbat_ai_memmap.ml`** (extend): the cell and itree widenings gain a `widen_join` plain form; the `extrapolate_steps ~steps` form is added for the selective path.
- **`cbat_ai_representation.ml`** (extend): `selective_widen_extrapolate : need:Var.Set.t -> reach_mem:bool -> steps:int -> t -> t -> t` — the AI-level entry point that composes `need` (Q3) with the word-lane consumption and the memory-lane plain widening (Q5).
- **`cbat_vsa.ml`** (modify): at the head-widening call site (line 2789), read `current_lm_head` (bound by `denote_block_with_stores` — T04), call `Cbat_landmarks.lm_advance head` (Listing 2), then `let steps = lm_calc_steps head in`, then `selective_widen_extrapolate thresholds ~need ~steps old incoming` (the new entry point). The `Cbat_thresholds.collect` call (line 2674) and the `selective_widen_join_threshold` call (line 2789) are removed at Stage 3.
- **`cbat_vsa.ml:meet_var`** (modify, T05): when the meet produces Bottom, call `Cbat_landmarks.observe_unsat` with the previous `p` and the guard `cstr`. The WordSet exposes a query for "which bounds in `cstr` are violated by `p`?" (to be added if not present — see §8 implications below).

### §8 implications for the acquisition path

§8 forbids "structural `match` patterns over BIL constructors" and inspecting memory operands directly. The acquisition path's natural implementation is:

```ocaml
(* In meet_var, when the meet produces Bottom: *)
let violated = WordSet.violated_bounds p cstr in  (* new query: list of (inequality, dist) *)
List.iter (fun (ineq, dist) ->
    Cbat_landmarks.observe_unsat ~inequality:ineq ~distance:dist
  ) violated
```

The `WordSet.violated_bounds` query is a pure abstract-value operation — it takes a `WordSet.t` (which is an abstract lattice value, not a BIL exp) and returns a list of bounds. It does not pattern-match on BIL. This is the §8-compliant way to implement per-bound acquisition.

**The `WordSet.violated_bounds` query is the one §8-driven API addition** to the WordSet module. It is small (≤ 30 lines) and its implementation lives behind the WordSet's own abstract interface — it queries the per-`e ≤ c` bound of the WordSet (which already exists in some form — `WordSet.bound : exp -> word option` or similar) and compares to the candidate bound. If this query does not already exist, it must be added as a T05 prerequisite.

### API shape (Q10 settled: separation, not consolidation)

- `Clp.widen_join : t -> t -> t` — plain Cousot-Halbwachs widening (no threshold, no landmark).
- `Clp.extrapolate_steps : steps:int -> t -> t -> t` — Listing 4.
- The lattice interface (`cbat_lattice_intf.ml`) remains 2-arg `widen_join : t -> t -> t`; the `extrapolate_steps` is a CLP-specific addition.
- The `test_cbat.ml:995, 7813` comments ("extrapolate_steps API was consolidated into widen_join") are **rewritten** to reflect the re-introduced separation.

### Memory at a head (Q5)

At a head widening, memory cells in `need` are widened via `Mem.widen_join` (plain, no threshold, no landmark). Memory carries no landmarks. The precision cost vs. the threshold path is acceptable per Q4 (semantic harness is the oracle).

### Consumption scope (Q3)

`AI.selective_widen_extrapolate ~need ~steps` applies landmark consumption only to vars in `need`. The `need` set is computed exactly as today (the existing `equal_need` infrastructure, the `~need` argument of the current `selective_widen_join_threshold`). The composition is: per var, if `need` → word lane with `extrapolate_steps` (or `widen_join` plain if `steps = ∞`); else → fall through to the existing widen. For memory cells, regardless of `need`, plain `Mem.widen_join`.

### Acquisition granularity (Q7: per-bound, all violated)

When a meet produces Bottom, *every* bound in `cstr` that is violated by `p` contributes a landmark. Over-recording is conservative (more landmarks → smaller `steps` → less extrapolation → more plain widening; sound). The closest-bound rule from the v1 spec is **rejected** (it would drop the further-out inequalities whose distances are the consumption signal — see the spec discussion).

### Cleanup (Q9: clear `H` + strict descendants)

After consumption at head `H`, the landmark table entries for `H` and all strict descendants of `H` in the WTO tree are cleared. The Bourdoncle WTO order is "inner before outer," so when `H`'s widening fires, all inner cycles have already been stabilized. Their landmarks are obsolete and would be cleared now or by their own consumption.

### The new 1000-iteration binary

`src/progs/landmark_loop_1000.c`:

```c
/* landmark_loop_1000.c — a counter loop bounded at K=1000.
   Purpose: external-behavior oracle for landmark convergence.
   With the threshold ladder (pre-fix): the geometric family 8*2^k
   has a rung at 1024, so the head bound widens to ~1023. With
   landmarks (post-fix): the head bound stabilizes at exactly 1001
   (the true least fixpoint: i ranges over [0..1000] at the head).
   Compiled PIE by compile_corpus.sh. */
#include <stdio.h>

volatile int g_sink = 0;

int main(void) {
    int i = 0;
    while (i < 1000) {
        g_sink = i;          /* prevent dead-code elim of the body */
        i = i + 1;
    }
    printf("%d\n", i);       /* prints 1000 at runtime; the VSA-bound is 1001 */
    return 0;
}
```

The choice of `K = 1000` is intentional: it sits *just below* the geometric rung `8*2^7 = 1024`, so the pre-fix threshold ladder pins the head bound to 1023, which is *24 above* the true fixpoint. With landmarks, the fixpoint converges at 1001. The gap (1023 vs 1001) is large enough that any regression to the threshold path is caught by the test.

The `g_sink = i` write prevents gcc from optimizing the loop into `i = 1000` (which would make the loop dead). The `volatile int g_sink` is the canonical trick to force a memory write that the VSA tracks.

The `printf("%d\n", i)` at exit gives the semantic harness a runtime value to byte-diff. The lifted binary must print `1000` (the runtime value) regardless of the VSA's bound; the VSA's bound is checked separately by the unit test on the lifted IR.

### Validation gate contract per stage

- **Stage 1** (API split): `dune runtest` 3 FAIL (unchanged — the threshold path is still active); `run_corpus.sh` 31/31 rc=0; `check_allocas.sh` 124/0; `run_semantic_all.sh` no worse than 28/3; `run_semantic.sh` 8/8. Net: **no behavior change**, gates unchanged.
- **Stage 2** (acquisition + consumption built but not consulted): gates unchanged (3 unit failures, etc.). New: a debug probe (`zz_scratch_probe/lm_paper_debug.exe`) that exercises the paper's §3 string-buffer CFG and asserts the landmark table fills across iterations; the probe lives in the `vsa-debug` profile only.
- **Stage 3** (switch, delete, unstub): `dune runtest` 0 FAIL; `run_corpus.sh` 32/32 rc=0 (31 existing + new `landmark_loop_1000`); `check_allocas.sh` 125/0; `run_semantic_all.sh` no fewer than 28/3 (the 3 pre-existing failures stay); `run_semantic.sh` 8/8. AGENTS.md validation table updated with a fresh timestamp.

### AGENTS.md / CONTEXT.md / ADR updates

- **AGENTS.md §Widening** (lines ~214–237): rewrite the "Widening is LANDMARK-DIRECTED… landed 2026-08-23" paragraph to describe the new code accurately. Remove the v1 "v2 replaced the v1 'rung-extension + two-pass restart' sketch" language (it referred to a non-existent intermediate).
- **AGENTS.md §Widening** (~L232): restore the "Clp.extrapolate_steps" line as a description of a real entry point (Q10 chose separation).
- **AGENTS.md "CURRENT VALIDATION STATE"**: re-measure all gates at the Stage-3 commit and rewrite with fresh numbers and a fresh timestamp.
- **CONTEXT.md**: add glossary terms (Landmark, Landmark Acquisition, Landmark Consumption, Widening Point, Standard Widening, Extrapolation); update the avoid-terms list (delete "threshold ladder", "rung", "hemisphere gate", "strict-rung rule").
- **ADR 0002** (`docs/adr/0002-landmark-directed-widening.md`): context (paper, doctrine, why we deleted the threshold ladder); decision (acquisition at `meet_var` per violated bound, consumption at WTO heads via `selective_widen_extrapolate`, cleanup clears `H` + strict descendants); consequences (corpus numbers may move per Q4, LM F1 unit test passes, AGENTS.md and CONTEXT.md updated).

### Risks

- **WordSet API gap**: the `WordSet.violated_bounds` query may not exist. If adding it requires deep changes to the WordSet's representation, the scope grows. Mitigation: in the worst case, fall back to a "best-effort" acquisition (record the violated-inequality at the granularity the WordSet exposes, even if it means fewer landmarks). Soundness is preserved; precision is reduced.
- **Stage 3 corpus/semantic regression**: if the switch from threshold to landmark causes a corpus or semantic regression, revert T08-final (the call-site change) and use the Stage-2 debug probe to find the offending binary. The fix is to tighten the consumption rule, not to re-enable thresholds.
- **Stage 3 unit-test failure**: if LM F1 doesn't pass after unstubbing, the consumption math is wrong, not the test. Fix the consumption; do not re-enable thresholds.
- **T09 (deletion) leaves dangling references**: `grep -r 'threshold' src/cbat_vsa/` is the gate. `dune build` is the second gate.

### Rollback paths

- **Stage 1**: revert the API split. Pre-stage-1 state had the threshold widening.
- **Stage 2**: revert the 6 stage-2 commits. Pre-stage-2 state had the threshold widening; nothing else changed.
- **Stage 3a (T08-final only)**: revert the call-site change. Stage-2 machinery stays; threshold widening returns.
- **Stage 3b (T09 deletion)**: revert the deletion. The threshold-widening functions are restored; the call site reverts to the threshold call.
- **Stage 3c (T14 unstub)**: revert the unstub. Tests go back to `(stub)`.

---

## Testing Decisions

### What makes a good landmark test

Tests assert **external behavior**: the head-state bound of the loop counter after the fixpoint, the soundness of `widen_join` (join ⊆ result), the round-trip of acquisition + consumption in a synthetic CFG. Tests do **not** inspect the landmark table directly (the table is implementation detail; the convergence behavior is the contract).

### The unit tests (Lane Z v2 unstubbing)

The existing scaffolding at `test_cbat.ml:7695` (`lm_jle_loop`) is the fixture builder. The unstubbed tests are:

- **LM F1** (K = 100 counter loop): the head-state bound stabilizes at exactly K + 1 = 101.
- **LM F1-acquire** (new): the fixpoint records at least one landmark with `dist_p` finite and `dist_c < dist_p` (i.e. the acquisition path is actually filling the table).
- **LM F2a** (`Clp.widen_join` soundness, 5 instances): for each, `p1 ⊑ p1 ∇ p2 ∧ p2 ⊑ p1 ∇ p2`.
- **LM F2c** (two-loop K1 = 40, K2 = 100): loop 1's head bound stabilizes at 41, loop 2's at 101.
- **LM F1-K1000** (new): the same `lm_jle_loop` but with `k1 = (w32 1000)` — the unit-test analog of the new corpus binary. Verifies the K = 1000 case is correct before committing to the corpus binary.

### The corpus binary test

- The new binary `landmark_loop_1000` is added to `/tmp/corpus/` by `compile_corpus.sh`.
- A new unit test (`test_cbat.ml` or `test_cbat/test_relevance.ml`) lifts the binary and asserts the VSA's bound on the head-state `i` is exactly 1001.
- A new entry in `check_allocas.sh`'s allowlist (or the structural asserts hold by construction).
- A new entry in `run_semantic_all.sh`'s run list.

### Debug probe

`zz_scratch_probe/lm_paper_debug.exe` (new): runs the paper's §3 string-buffer CFG (a synthetic sub built in OCaml) and asserts the landmark table fills across iterations. Lives in the `vsa-debug` profile only; never installed; per AGENTS.md principle #6.

### Prior art

- The existing Lane Z v2 scaffolding in `test_cbat.ml:7695-7784` (`lm_jle_loop`).
- The existing `cbat_ai_representation` test infrastructure (the `mk_caller_alias` / `mk_dummy_sub` patterns).
- `scripts/run_corpus.sh` (31/31 rc=0 baseline) and `scripts/run_semantic_all.sh` (the 8/8 oracle).
- `.scratch/landmark-directed-widening/issues/01-19` (the v1 issue map — most apply directly; the §8 / 230b6c4-era issues are minor extensions).

---

## Out of Scope

- The 3 pre-existing semantic regressions (`out_nested_struct`, `out_va_arg_vacopy`, `out_variadic`); tracked under `.scratch/one-frame-anchor-removal/`.
- The `mem_access_via_ptr` §8 violation in `src/bil2llvm.ml:196-206`; flagged in the 230b6c4 commit message; deferred.
- The FP intrinsics (issues 10-13 in the v1 spec) and the COMISS/COMISD table — already landed 2026-08-25.
- The `restore_sp_after_call` work and the b5 fixture — already part of the 230b6c4 baseline.
- Re-implementing the Simon & King paper from scratch — we port Listings 1-4 faithfully per the paper, with the AGENTS.md §8 constraints.
- The lost pi session `01a03eb4` — sunk cost; the source of truth is now the paper + AGENTS.md doctrine + the v1 spec + this v2 spec.

---

## Further Notes

- **Source of truth**: this spec is the canonical design for the landmark workstream at the 230b6c4 baseline. The v1 spec (`.scratch/landmark-directed-widening/spec.md`) is read for the original rationale but is superseded by this v2 for implementation.
- **Tickets**: this spec is split into implementation tickets via `/to-tickets` after acceptance. The ticket graph is the 3-stage plan (Stage 1 = T06 + T07a/b, Stage 2 = T01 + T02 + T03 + T04 + T05 + T08-mid, Stage 3 = T08-final + T09 + T14 + T19 + the new 1000-iter corpus binary + the K=1000 unit test).
- **The 1000-iter binary is the keystone regression test**: it lives in the corpus (real binary, real IR, real semantic check) AND has a unit-test analog (`LM F1-K1000`) that doesn't require the binary. Either side catches a regression; both together give high confidence.
- **Docs/code divergence risk**: AGENTS.md says "landmarks landed 2026-08-23." At Stage 3, either the code matches the claim (ideal) or AGENTS.md is corrected. The Stage-3 commit message + this spec's ADR 0002 + the new AGENTS.md validation row are the three places where the claim is anchored to the code.
- **§8's reach**: the new `WordSet.violated_bounds` query is the only API addition the §8 doctrine forces on the WordSet module. Everything else (the new entry points, the cleanup, the consumption math) is §8-clean by construction (operates on abstract values, not BIL).
