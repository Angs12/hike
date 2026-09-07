# Variable-Bounded Ranges (VLA + Variadic Handling)

**Status:** spec (grilled 2026-09-04 across 6 rounds; implementation NOT started)
**Triage:** ready-for-agent
**Tree:** `affine-equalities` @ `ec8c17d` (builds on the fused Affine Equalities Domain, the revived VLA kind, the classify-time membership rule, and per-region scoping)
**Supersedes:** `.scratch/affine-equalities/spec.md` (the constant-only cut — its bound language is expressible but no feeder writes variable bounds; its `alloca_vla ≥1 region` acceptance is unmet structurally)
**Revisits:** ADR-0006 (the VLA kind is removed; variable floors travel on the generalized Range)
**Related, untouched:** review #3 items #7 (narrowing), #8 (packing/relational consumers — the deferred guard-cap feeder belongs to it), #10 (acceleration)

## Problem Statement

A dynamically-sized stack allocation (VLA / `alloca`) still defeats region conversion on real binaries: the bound language can name a variable in a bound, but no feeder ever writes one, so every live bound is constant-only — and on the real `alloca_vla` binary not even the constant path fires (sizes flow through division/shift alignment chains; dynamic stores are loop-counter-indexed). Variadic-argument traffic (the `va_arg` register-save-area walk) is unrepresentable for the same reason: a walk bounded by a runtime size has no nameable extent. The result is the whole-sub fallback and surviving `Unbounded` diagnostics wherever a bound is genuinely a variable.

## Solution

Generalize the Range classification itself to carry `const | var + k` bounds on each side and remove the VLA kind: dynamic extents become variable-floored ranges ordered by allocation sequence (read off the already-composed frame expression, free), merged by may-subset in the split plan, and decided by a demand-driven ordering solver (canonicalize → live value sets → construction order → Unbounded) reserved for dynamic-vs-loaded comparisons — the variadic shape. The guard-cap feeder stays deferred behind its named home until a failing def earns it. Static regions above a dynamic extent convert for any size; overlapping regions stay memory. No emitter retyping or new lanes: the only emitter diff is the ticket-05 arm-deletion fallout (Range patterns narrow to Const, the producer-less VLA arm deletes), routing stays tag-driven on the existing rebind path.

## User Stories

1. As a lifter user with VLA/alloca code, I want disjoint static locals to become real LLVM allocas even when the same function uses dynamic allocation, so that LLVM can optimize them.
2. As a lifter user, I want the dynamic allocation itself to keep working exactly as today (runtime-sized LLVM alloca), so that nothing regresses while static regions convert around it.
3. As a lifter user with variadic (`va_arg`) code, I want the register-save-area walk to resolve to a variable-floored range when its offset is bounded, so that variadic functions stop degrading to Unbounded.
4. As an analyst reading diagnostics, I want `Unbounded` warnings to disappear where an address genuinely resolves into a variable-denominated extent, so that surviving warnings stay trustworthy.
5. As an analyst, I want `Unbounded` warnings to REMAIN where an address does not resolve, so that no warning is silenced without an emission target.
6. As a VSA maintainer, I want extent-vs-extent ordering to come from allocation sequence with zero new facts, so that the solver only ever runs on dynamic-vs-loaded comparisons.
7. As a VSA maintainer, I want region merging driven by may-subset (always sound in the split plan), so that fusing potentially-aliased cells never needs a must-proof.
8. As a VSA maintainer, I want widening to translate only constant offsets and preserve variable identity (collapsing on var redefinition), so that loop-carried sizes degrade soundly without renaming analysis.
9. As a reviewer, I want the kind removal to land in two steps (variable floors alongside, then arm deletion), so that every commit stays green and bisectable.
10. As a reviewer, I want the guard-cap feeder to stay deferred with its home named, so that unneeded machinery does not ship on speculation.
11. As a gate keeper, I want `alloca_vla` converting ≥1 disjoint region with byte-identical stdout, so that the feature is proven on a real binary.
12. As a gate keeper, I want fixture-level proof for variadic shapes plus a diagnostic-shrink count on the mixed variadic binary, so that variadic progress is measured without bundling the unrelated T02/T03 bug classes.
13. As a gate keeper, I want the 8/8 semantic harness and both 30/2 semantic gates to stay green, so that precision work never trades correctness.
14. As a future extender, I want the demand-driven ordering solver to be the single home for bound comparison, so that a future guard-cap layer plugs into one seam.

## Implementation Decisions

- **Representation: generalize Range, delete the VLA kind.** Bounds become `const | var + k` per side, independently. The extent payload folds into variable-floored ranges; the kind removal lands in two steps (floors alongside the kind first, arm deletion once no producer emits it). Spans stay `int64` display-only constants; the split plan reads variable floors directly for overlap, and no conversion decision reads a span where a variable floor exists.
- **Allocation sequencing is free.** Stacked decrements compose into one frame expression recording their order; canonicalizing two dynamic addresses to `(root, offset)` via the existing equality union-find exposes extent-vs-extent order as constant arithmetic. No sequence field, no def walk. Cross-allocation var-vs-var ordering never arises.
- **Merging by may-subset in the split plan.** Two ranges fuse when either may be a subset of the other — over-merging costs precision, never correctness. The survivor keeps the lower low; the high side collapses to Unbounded unless one high var's live value set is a subset of the other's (the subset read applied recursively).
- **Demand-driven ordering solver, queries only.** Canonicalize (equality substitution, step zero) → live value sets → construction order → unknown. The solver is a pure query function; nothing in the fixpoint loop changes. Unknown collapses the caller to Unbounded (the sound identity).
- **Widening splits as before, extended.** Bounds extrapolate through the landmark machinery; variable identity is preserved while only constant offsets translate; a redefined denominating var collapses its bound to Unbounded.
- **Membership emits variable floors.** The shared-variable verdict logic survives with only the emitted value changed (`Range(anchor-s, anchor)` instead of the kind); the finite cap is dropped, not re-derived — the uncapped extent is already the sound rule.
- **Guard-cap feeder deferred.** The named home stays; the feeder ships only when a named failing def requires it. Live sets plus allocation sequencing carry the first cut.
- **No emitter retyping or new lanes.** The rebase-GEP lane stays dropped; emission remains tag-driven on the existing rebind path.

## Testing Decisions

- A good test pins observable behavior through the highest seam: emitted IR bytes, diagnostic lines, and pass/fail gates — never abstract-state internals.
- **Unit level:** bound-syntax fixtures (const/var floors, joins with var mismatch collapsing soundly), canonicalization fixtures (same-root constant decisions, chain composition), solver fixtures per layer with unknown-collapses pinned, merge-survivor fixtures over bound pairs without any fixpoint.
- **Prior art:** the AE- fixture family, the V1–V29 membership pins (V29 spill end-to-end stays green through the rewrite), the S1–S8 scoping pins (S8 re-targeted from the kind to variable floors), the C4/R11 merge-hull pins, the F1-NEQ strict test.
- **End to end (mandatory per repo doctrine):** unit suite green, corpus 32/32 rc=0 with IR-identity vs pre-change control except the intended conversion deltas, structural asserts, 8/8 semantic harness, both 30/2 semantic gates, plus `alloca_vla` converting ≥1 disjoint region with identical stdout and the `va_arg_mixed` diagnostic-shrink count.
- **Dark-step bar:** the floors-alongside step is battery-green with zero behavior change (no producer emits floors yet); all behavior change lands in the generalization step.

## Out of Scope

- The guard-cap feeder itself (deferred to a failing def; review #8 territory).
- Octagon/polyhedral grades, disjunctive (multi-alternative) bounds.
- Loop-bound reasoning for index expressions (`i*4` counters stay as today until the NEQ-guard gap closes).
- Emitter retyping or new lanes (region spans stay int64); the ticket-05 arm-deletion narrowing already landed as kind-removal fallout.
- Stride/mask/wraparound preservation (conceded, tripwired, falsifiable as before).
- `va_arg`/variadic tickets T02/T03 turning green (pre-existing multi-cause failures; this spec measures diagnostic shrink, not gate passage).
- Cross-allocation var-vs-var inequality proving (proven unnecessary — allocation sequencing decides).

## Further Notes

- The subset question resolved as: consumers read the denominating var's live value set and decide by subset — no ordering facts are ever fed. If that ever proves insufficient, the guard-cap home is named and waiting.
- The motivating chain `(0,8),(8,16),(16,h1)` with `h1 ≥ 16` free is carried by construction order inside the solver (layer three), not by a feeder.
- Seams for confirmation: (1) the generalized bound syntax in the domain vocabulary; (2) the demand-driven solver as the single comparison home; (3) the split-plan overlap read of variable floors; (4) fixture-level tests with IR-identity as the top gate. No new pass, no pipeline change.
- Grilling record: 6 rounds, 2026-09-04 — VA fixed as variadic-argument traffic; guard caps chosen then deferred by the stack-ordering insight; representation fixed as Range-generalization with kind removal; merging fixed as plan-side may-subset; widening fixed as offset-only translation.
