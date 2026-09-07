# Affine Equalities in the Fixpoint + VLA-as-Region

**Status:** spec (grilled 2026-09-03 across 8 rounds; implementation NOT started)
**Tree:** `review3-removals` @ `ece51ca`-plus (#1 landed after)
**Supersedes (partially):** review #3 item #2 (VLA-kind deletion — the kind is revived with a payload instead)
**Revisits:** ADR-0005 §1 (extraction stays post-pass; the *relations* move into the domain — see Further Notes; to be recorded as ADR-0006 on approval)
**Related, untouched:** review #3 items #7 (narrowing), #8 (packing/relational consumers), #10 (acceleration)

## Problem Statement

A dynamically-sized stack allocation (VLA / `alloca`) poisons the entire subroutine: one `RSP := RSP − size` with a non-literal size degrades the whole sub to the single-frame fallback, converting zero regions — measured on `alloca_vla` (0 `stack_rN` allocas vs 7 on a VLA-free twin, semantics identical either way). The VLA's extent is unnameable in the current vocabulary: kinds carry only constant `int64` bounds, so anything touching the dynamic size widens to `Unbounded`, and the split plan can only veto the whole sub, never scope around the dynamic extent.

## Solution

Track affine equalities (`x = y + k`) inside the VSA abstract state, fused with per-var bounds in one new domain module; revive the `VLA` kind with an `{anchor, max_size}` payload computed at extraction; and scope the whole-sub VLA veto down to per-region overlap against the VLA extent. Static ranges above a VLA's anchor convert for any size, including runtime (TOP) sizes; the dynamic access itself routes through the existing rebound-RSP dynamic-alloca lane. No new emitter lane.

## User Stories

1. As a lifter user with VLA/alloca code, I want disjoint static locals to become real LLVM allocas even when the same function uses dynamic allocation, so that LLVM can optimize them.
2. As a lifter user, I want the dynamic allocation itself to keep working exactly as today (runtime-sized LLVM alloca), so that nothing regresses while static regions convert around it.
3. As an analyst reading diagnostics, I want `Unbounded` warnings to disappear where an address genuinely resolves into a VLA extent, so that surviving warnings stay trustworthy.
4. As an analyst, I want `Unbounded` warnings to REMAIN where an address does not resolve, so that no warning is silenced without an emission target.
5. As a VSA maintainer, I want the affine bound language in one module with a tight deletion test, so that generality costs one small file instead of scaffolding smeared across four modules.
6. As a VSA maintainer, I want the frame relation and the bound language to share one expression syntax, so that the same affine lemma is never proven twice with two answers.
7. As a reviewer, I want the language to land dark (wired but unreachable, battery trivially green) before any behavior changes, so that each commit is independently green.
8. As a reviewer, I want wildcard matches to carry explicit conservative arms for the new kind before light-up, so that no behavior changes through a match hole.
9. As a gate keeper, I want IR byte-identity vs the pre-change control on the corpus plus the 102-binary coreutils set, so that equivalence is measured on real code, not just fixtures.
10. As a gate keeper, I want the 8/8 semantic harness and both 30/2 semantic gates to stay green, so that precision work never trades correctness.
11. As a future extender, I want inequality facts to have a named home (guard caps + construction orderings) even though only construction facts feed the language at first, so that growing the language doesn't require re-architecture.
12. As a future extender working on loop-carried VLAs, I want above-disjointness to hold without loop reasoning, so that per-iteration re-allocation needs no special case for scoping.

## Implementation Decisions

- **Placement: full relational, equalities-only, inside the abstract state.** Affine equalities (`x = y + k`) are tracked in the fixpoint, fused with per-var bounds in one new domain module in the domain library. Finite height over fixed vars (subspace dimension is bounded), so equalities join exactly and are never widened. Polyhedral/octagon grades are explicitly out; Miné's octagon paper is the recorded ceiling.
- **Coexistence by replacement with bounds preserved.** The fused domain replaces the interval word domain but carries per-var bounds inside itself (bounds-only interval half: bounds kept, strides conceded — the F1-NEQ strict test and landmark corpus tags are the named tripwires for the stride concession). Strides are falsifiable fast once fixtures run.
- **Widening splits per component.** Bounds extrapolate through the existing landmark machinery byte-identically (forensics keep working); equalities pass through joins untouched. The landmark code never sees a relation.
- **Reduction at joins + queries only.** Equalities and bounds communicate where states merge and where answers are consumed (classify-time queries reduce for themselves). Transfers stay single-component-cheap; no dirty tracking. Consumers (first: the membership rule) carry the reduce-for-yourself burden knowingly.
- **New file for the fused domain** in the domain library (clean seam, standalone fixture tests with zero production touch as the first green step); the abstract state becomes a thin importer in the second step.
- **Kind revival as a record payload** (`VLA` of `{anchor, max_size}`) through the three-site type edit (definition, signature mirror, vocabulary alias — compiler-checked), wiring the currently dead optional tid parameter at the single `classify` call site from data `extract` already holds.
- **Anchors computed at extraction** by prefix-denoting RSP at the decrement def, in entry-SP-relative coordinates (0 prologue, negative mid-function) — the same site and idiom as the existing size bounds.
- **Scoping, not veto.** The whole-sub dynamic-alloc veto becomes per-region overlap against the VLA extent `(-inf, anchor]`, refined to `(anchor-hi, anchor]` for finite caps. Regions above the anchor convert for any size. VLA-tagged defs are exempt from the inside-or-disjoint check (the dynamic lane owns them). No loop gate for above-disjointness (later iterations only extend downward); finite-floor use gated to non-loop decrements if ever.
- **Emission routing is tag-driven on the existing rebind path** (traced: the dynamic-alloca base already feeds the model-RSP phi, so rebound-relative arithmetic lands in the real alloca). The planned rebase-GEP lane is dropped. Regions overlapping the extent stay memory, never per-region allocas. No emitter changes in the first commit.
- **Bound language scope: general affine, construction-facts only.** Bounds name constants, single dynamic vars, and guard-cap facts; order facts are anchor≤var non-emptiness. No relational fact source exists beyond construction (the engine is non-relational — that is review #8's territory), so generality beyond the VLA chain is admitted scaffolding, bounded to the one small module.
- **Membership rule (light-up):** shared-variable recognition (decrement size var = address var, full value numbering per the grill) with const-k and symbolic-k-denominated offsets from the start, decided at classify time.
- **Dark-then-lit landing:** language + kind + equality + merge verdicts wired but unreachable first (battery trivially green), membership rule second (all behavior change, full battery).

## Testing Decisions

- A good test pins observable behavior through the highest seam: emitted IR bytes, diagnostic lines, and pass/fail gates — never abstract-state internals.
- **Unit level (new domain module):** join/meet/equal/transfer/reduction fixtures, including stride-sensitive fixtures that name the conceded precision explicitly; merge-verdict fixtures over bound pairs without any fixpoint.
- **Prior art:** the `R12` region-behavior family and `C4a/C4b/R11` merge-hull pins (extend to mixed static/dynamic components); `F1-NEQ` strict test (stride tripwire); `D0-D5` DCE seam tests.
- **End to end (mandatory per repo doctrine):** unit suite green, corpus 32/32 rc=0 with IR byte-identical to a pre-change control, structural asserts, 8/8 semantic harness, both 30/2 semantic gates, plus `alloca_vla` converting ≥1 disjoint region with identical stdout; coreutils 102-IR byte-identity as the real-code equivalence gate.
- **Dark-step bar:** battery trivially green with zero behavior change (no new reachable behavior, only new code).

## Out of Scope

- Octagon/polyhedral grades, inequality tracking through the fixpoint, hull/Chernikova machinery.
- Loop-bound reasoning for index expressions (`i*4` counters stay `Unbounded` until the NEQ-guard gap closes).
- Emitter changes of any kind in the first two commits (rebase-GEP lane explicitly dropped).
- Retyping `region.span` to bound expressions (verdicts live in the model; spans stay `int64`).
- Stride/mask/wraparound preservation inside the fused domain (conceded, tripwired, falsifiable).
- `va_arg`/variadic tickets T02/T03 (pre-existing failures, unchanged).
- The `sas11.pdf` reference (UNREAD — PDF unfetchable, title unconfirmed; needs a text copy before it can bear on anything).

## Further Notes

- The variable-bound debate resolved as: an unconstrained variable floor decides exactly what `-inf` decides; the user's `(0,8),(8,16),(16,h1),(h1,h1+16)` example showed the real power is variable-*denominated* ranges ordered by construction facts (`h1 ≥ 16` free) — which the general language covers and `-inf` cannot name.
- ADR-0005's post-pass rationale is partially revisited (relations move into the domain; the extraction *walk* stays post-pass). Record as ADR-0006 on spec approval.
- Report: `/tmp/architecture-affine-20260903-155921.html` (6 cards, verified paper table).
- Seams for confirmation: (1) new fused-domain file in the domain library; (2) abstract-state seam for wiring; (3) `Cbat_extraction` + vocabulary alias for the kind; (4) model-only verdicts (emitter stays a pure consumer); (5) fixture-level tests, IR-identity as the top gate. No new pass, no pipeline change.
