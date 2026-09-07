# Handling VLA: the Four-Lock Ladder (alloca_vla converts)

**Status:** spec (grilled 2026-09-04 across 4 rounds + fact-finding dissection + prior-art research; implementation NOT started)
**Triage:** ready-for-agent

**Status:** spec (grilled 2026-09-04 across 4 rounds + fact-finding dissection + prior-art research; implementation NOT started)
**Triage:** ready-for-agent
**Tree:** `var-bounds` @ `f4683a2` (variable-bounded ranges, ordering solver, kind deletion — all merged)
**Supersedes (partially):** `.scratch/var-bounds/spec.md` (its `alloca_vla ≥1 region` acceptance, structurally unmet there — this spec is the ladder that meets it)
**Related:** `.scratch/affine-equalities/spec.md` (the constant-only cut); review #3 items #8 (relational consumers), #10 (acceleration)

## Problem Statement

Two stacked dynamic allocations in one subroutine (the measured shape: a 32B VLA and a 48B `alloca`, both bare decrements with sizes recomputed upstream) keep every stack access — static and dynamic alike — in the single-frame fallback: zero `stack_r` regions, zero variable floors firing corpus-wide, 19 `Unbounded` defs. The dissection proves four independent locks, not one big problem: the verdict dies at spill Loads (7 of 8 dynamic defs linearize structurally), the align-up idiom (division, scaling, masks) severs size chains, the escape rule vetoes the merged region on the same spill traffic, and the merged hull needs floors before it can split. Each lock is named, counted, and fixable inside the affine fragment.

## Solution

Four tickets in merit order, each with a counted payoff on the dissecting binary: a bounded single-spill equality rule (verdict 0/8 → 7/8); bounds-side transfer arms for the align-up idiom (const-division scaling, align-mask intervals — equality still severs, bounds carry the facts); the same spill distinction at the escape rule (shared predicate, or nothing converts); and the flagship-region isolation (`buf`-above-both converts by allocation sequence once floors fire). Runtime division, true extracts, and flag semantics stay havoc with their current backstops. No emitter changes; the dynamic lane already emits its runtime-sized allocas.

## User Stories

1. As a lifter user with VLA/alloca code, I want the static locals above the dynamic extents to become real LLVM allocas, so that LLVM can optimize the non-dynamic majority of the frame.
2. As a lifter user, I want each dynamic allocation to keep its working runtime-sized LLVM alloca with its traffic rebound onto it, so that dynamic behavior is byte-identical while statics convert around it.
3. As a lifter user, I want spilled size variables to keep their equalities through one stack cell, so that ordinary register-pressure spills do not blind the analysis.
4. As a lifter user with aligned allocations, I want the align-up idiom (division, scaling, masking) to feed bounds even where equality severs, so that aligned sizes stay ordered instead of collapsing.
5. As an analyst reading diagnostics, I want the 19 `Unbounded` defs on the dissecting binary to shrink to exactly the unknowable set (runtime divisors, true extracts, flag semantics), so that every surviving warning names a real analysis boundary.
6. As a VSA maintainer, I want the spill rule bounded to one cell and one load/store pair, so that memory-indexed equality never becomes a second alias analysis.
7. As a VSA maintainer, I want the escape rule and the verdict to share one spill predicate, so that the blessed traffic is never vetoed by the sibling rule.
8. As a VSA maintainer, I want operator arms split by side (exact equality arms vs over-approximate bounds arms), so that each arm's soundness argument is checkable in isolation.
9. As a reviewer, I want the isolation experiment first (artificially fire the verdict, dump the plan), so that a fifth unnamed rule surfaces before the ladder is built, not after.
10. As a reviewer, I want each lock landed and measured separately, so that any step with zero payoff stops the ladder.
11. As a gate keeper, I want `alloca_vla` converting ≥1 disjoint region with byte-identical stdout, so that the feature is proven on a real binary.
12. As a gate keeper, I want the 8/8 semantic harness and both 30/2 semantic gates green throughout, so that precision work never trades correctness.
13. As a future extender, I want the residual risk (whether `buf` isolates or a fifth rule appears) recorded with its experiment output, so that the next design starts from measurement.

## Implementation Decisions

- **Experiment zero: artificial verdict firing.** Before building, force floors on the 7 linearizable dynamic defs, dump the region plan, and check whether `buf`-above-both isolates. If a fifth rule appears, it becomes ticket zero; if `buf` isolates, the ladder's payoffs are confirmed as stated.
- **Lock 1 — bounded single-spill equality.** A spilled variable keeps its equality through one stack cell and one load/store pair while the cell's base is untouched (the Astrée/Mopsa cell rule and VSA a-loc identity are the shipped precedents). A store to an unknown offset folds the cell and kills the equality. No general memory reasoning.
- **Lock 2 — bounds-side arms for the align-up idiom.** Const-division feeds interval scaling, align-masks feed `[x−(2^k−1), x]`, same-root/const-side concat folds exactly, shr shifts bounds; equality severs on all of them (correctly — none is affine). Runtime division, true extracts, and flag chains stay havoc. No congruence revival: bounds-side intervals already order the idiom against constants, and stride revival reopens the conceded F1-NEQ tripwire.
- **Lock 3 — shared spill predicate at the escape rule.** A spill to a dead cell is not an escape. One predicate serves the verdict and the escape check; landing Lock 1 without Lock 3 converts nothing (the plan stays vetoed on the same traffic).
- **Lock 4 — flagship isolation by allocation sequence.** With floors firing, the above-both-anchors statics isolate by the composed frame expression (canonicalize to root+offset — constants decide). No solver involvement for the flagship; the solver stays reserved for dynamic-vs-loaded comparisons.
- **Merit order is the landing order** (spill → bounds arms → escape → isolation proof), each measured against the dissecting binary before the next lands. A step with zero measured payoff stops the ladder for re-grilling.
- **No emitter changes.** Routing stays tag-driven on the existing rebind path; the dynamic lane's runtime-sized allocas already emit.

## Testing Decisions

- A good test pins observable behavior through the highest seam: emitted IR bytes, tag dumps, diagnostic lines, and pass/fail gates — never abstract-state internals.
- **Experiment zero** runs through the tag-dump probe over the rebuilt corpus binary (ALL-sub mode), comparing region plans verdict-off vs verdict-forced.
- **Unit level:** single-spill fixtures (spill keeps equality; unknown-offset store kills it; two-cell chains stay havoc); bounds-arm fixtures per operator (const-div scaling, mask intervals, same-root concat, shr shifting) with havoc pins for runtime-div/extracts/flags; shared-predicate fixtures (spill-to-dead-cell escapes nothing); isolation fixtures (stacked decrements, above-both converts).
- **Prior art:** the AE-/VB-/V-/S-fixture families, the V29 spill end-to-end precedent, the S8 stacked-extent pin, the F1-NEQ strict test (guards the no-congruence line), the dump_tags ALL-sub mode from the VB-04 investigation.
- **End to end (mandatory per repo doctrine):** unit suite green, corpus 32/32 rc=0 with IR-identity vs pre-change control except intended conversion deltas, structural asserts, 8/8 harness, both 30/2 gates, `alloca_vla` ≥1 region with identical stdout, per-lock payoff counts refreshed in the validation state.

## Out of Scope

- Runtime-division, true-extract, and flag-chain precision (unknowable in-fragment; havoc + backstops stay).
- Congruence/stride revival (the F1-NEQ concession stands).
- General memory-indexed equality (a second alias analysis by another name).
- Octagon/polyhedral grades, disjunctive bounds.
- The guard-cap feeder (still deferred to a failing def; this ladder does not need it).
- Loop-bound reasoning for index expressions (the loop-indexed dynamic stores stay as today).
- Emitter changes of any kind.

## Further Notes

- Measured baseline on the dissecting binary (fact-finder, 2026-09-04): 2 decrements (32B VLA + 48B alloca, bare `RSP := RSP − RAX`); 8 dynamic addr defs (7 linearizable, all spill-rooted; 1 TOP); 32 static-rooted usable relations; 18 never-linearizing flag/guard defs; 19 Unbounded (guards + 1 dynamic store + incr flags); one merged hull `(-64,268)` → r0 blocked by member-not-direct AND frame-escape; no missed ordering pair among tagged ranges.
- Prior-art verdict (research, 2026-09-04): only Rugina–Rinard (whole-program dynamic regions) and SCEV (loop-scoped) shipped dynamic-extent ordering from affine facts; price is linearity + widening amnesia + evaporation at non-affine ops. VSA stayed non-relational on cost (thousands of a-locs).
- The residual risk is one experiment, not a program: whether `buf` isolates once the verdict fires, or a fifth rule surfaces.
- Seams for confirmation: (1) the mirror transfer (spill rule + bounds arms — one module, per-arm soundness); (2) the shared spill predicate serving verdict + escape; (3) the existing split-plan overlap read (unchanged — floors arrive, logic stands); (4) tag-dump + IR-identity as the top gates. No new pass, no pipeline change.
