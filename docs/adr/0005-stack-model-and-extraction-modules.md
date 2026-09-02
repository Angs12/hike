# ADR 0005: the stack model and the tag extraction get their own modules

Date: 2026-09-02 · Status: accepted · Supersedes: none (extends Finding 1's "one producer" and the
2026-09-02 architecture review's candidates #1/#6)

## Context

`vsa_info`'s producer was split across four modules: `hike_vsa.ml` re-walked the sub's defs with
VSA primitives to classify offsets (a ~200-line walk that duplicated the M6 meet discipline with
`test_cbat/precision_probe.ml`'s copy), then called INTO `hike_stack_to_locals.ml` for regions and
the split plan — so "the VSA result" spanned convutils (types) + hike_vsa + stack_to_locals +
hike_kb (transport) before any consumer read it. `hike_stack_to_locals.ml` itself bundled two
different kinds of code: the pure DECISIONS (regions/plan/escape/ABI-visibility — no KB, no
Project, no pass state) and the REWRITE PASS (the Exp.mapper conversion).

## Decision

1. **`Cbat_extraction`** — a submodule of `cbat_vsa.ml` (NOT a sibling file: the walk IS the
   fixpoint's own primitives, and the main module of a wrapped library is unreachable from its
   siblings — a cycle by construction; discovered by the build, recorded here): the M6
   classification walk over the CONVERGED solution (`st_tag_of` — the ONE home of the meet
   discipline; the probe's copy adopted the production gate, a git-proven accidental divergence),
   `kind` (the enum `Convutils.vsa_kind` aliases — one definition, one deriver), the k-range
   arithmetic, the set-overlap merge, and the VLA idiom (`vla_decrement_p` shared with
   `hike_vsa_relevance.detect_dynamic_alloc` — the SHAPE is one fact; the visitor's def-set role
   and the extractor's size role stay separate).
   A POST-PASS, deliberately not fused into the fixpoint: the walk's per-def state is a THIRD
   discipline (the sequential chain met with the block's converged IN-state values), and fusing
   it would pay per-visit cost and read mid-fixpoint states.
2. **`hike_stack_model.ml`** — the pure stack model (the four decision functions,
   `is_abi_visible`, `region_bytes` — closing the emitter's duplicate — the escape analyses,
   the whole-sub rules), split from `hike_stack_to_locals.ml`, which keeps the REWRITE PASS and
   imports the model. `hike.mli` exports `Stack_model` beside `Stack_to_locals`.
3. **The composition** — `hike_vsa.offsets_of_sub` is now:
   `fixpoint → Cbat_extraction.extract → Stack_model.{frame_escapes, regions_of_sub, split_plan}`;
   `vsa_info` is BUILT COMPLETE at one site. The degraded/non-converged arms and the
   100%-invariant gap WARN stay in hike_vsa (pass policy: warn + empty-info).

## Consequences

- All ~60 `Convutils.Range`-style constructor references compile unchanged through the alias.
- The probe routes its meet through `st_tag_of` (numbers re-baselined; the divergence of gates
  never differed on the corpus — byte-identity held).
- The merge with main (mem-fission et al.) takes the three commits separately if conflicts bite
  (extraction, model split, deriver — sliced per the grill for exactly this).
