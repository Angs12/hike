# Pins: Hike_origin

Module `hike_origin` (`src/hike_origin/hike_origin.ml`).
One row per pin in `test/unit/test_hike_origin.ml`.

The module is the origin leaf library: the ADT and its per-origin facts
table.  Red evidence is by review: each disable recipe is the textual
inversion of the pinned branch, and the pin's exact-equality assertion
fails under that inversion.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| ORI-01 | `facts Stack`: base = `segment_base` (2^62+8), certified 4, ±8 MiB clamps; the VLA frame rides the same segment span (its allocation lives on the frame line) | change `facts Stack`'s `base` to `0L` | pin FAILs: the base assert fails |
| ORI-02 | the ADT is total: five constructors, each with a name | drop a constructor from the `name` match | pin FAILs: the name assert fails (inexhaustible match) |
| ORI-03 | `origin`: a stack value reads `Some Stack`; a plain singleton, an absolute Clp, and a stack∪plain union read `None` | make `origin` answer `Some Abs` for `Clp _` | pin FAILs: the plain/absolute asserts fail |
| ORI-04 | same-origin ops keep the origin: union/meet of two stack values read `Some Stack` | make `union`'s same-origin arm materialise via `to_plain` | pin FAILs: the union assert fails |
| ORI-05 | the boundary refinement: a wholly window-side value (offsets ≥ word) refines to `Window`; a Vla-frame value inside its extent keeps the frame, one crossing out re-absorbs to `Stack`; a value spanning the entry line keeps `Stack`; plain passes through | drop the extent lookup in `refine_origin`'s `Vla` arm (always keep) | pin FAILs: the crossing assert (the re-absorb) fails |
| ORI-06 | the per-def origin stamp: a solved sub's window-side address def (`rsp+16`) reads `Some Window` through `Vsa.Def_origin.def_origin` | make `stamp_origin` stamp `Some Abs` unconditionally | pin FAILs: the stamped origin assert fails |
| ORI-07 | the store→load round-trip (frame): a stored `rsp−8` pointer reads back `Some Stack` through the solve seam | restore the load fold's `WordSet.bottom` seed (the join demotes the rel via `to_plain`) | pin FAILs: the read-back origin is `Some Abs` |
| ORI-08 | the store→load round-trip (window): a stored `rsp+16` pointer reads back `Some Window` | restore the load fold's `WordSet.bottom` seed, or drop `refine_origin` from `denote_def` | pin FAILs: the read-back origin is `Some Abs`/`Some Stack` |
| ORI-09 | the VLA seed: `rsp := rsp − rax` with a set-valued size stamps the decrement def's value `Vla T` (T = its own tid) at the TRUE entry-line positions [B−S], and records the extent [min(B−S), max(B)) in the seed table | make `vla_seed` return `p` (no seed) | pin FAILs: the stamp, the bounds, and the extent asserts fail |
| ORI-10 | +INT inside the extent shifts the offsets exactly and keeps the frame (`rsp±k` at the shifted offsets) | drop the `Add`/`Sub` wrap rows for a `Vla` operand | pin FAILs: both keeps-the-frame asserts fail |
| ORI-11 | a value crossing out of the extent re-absorbs to `Stack` at the boundary (positions unchanged) | make `refine_origin`'s `Vla` arm always keep the frame | pin FAILs: the stamps-Stack and positions asserts fail |
| ORI-12 | same-frame unions stay exact (`Wrap (Vla t)`); different-frame unions materialise (the cross-line absorb excludes Vla∪Vla) | make `cross_line` absorb `Vla ∪ Vla` too | pin FAILs: the different-frame assert fails |
| ORI-13 | a Vla value unioned with a Stack value wraps at Stack, both offset runs exact | make the cross-line absorb answer `Materialise` | pin FAILs: the reads-Stack and both-runs asserts fail |
| ORI-14 | the store→load round-trip (VLA): a stored VLA-frame pointer reads back `Some (Vla T)` with the same tid | restore the load fold's `WordSet.bottom` seed | pin FAILs: the read-back origin demotes |
| ORI-15 | the round-trip across a machine call: the saved pointer survives the call keep (the VLA-frame SP keeps from its extent's low end) | make `frame_keep` use the plain max-offset boundary for Vla SPs too | pin FAILs: the read-back origin is demoted |
| ORI-16 | the round-trip across a loop: the loop-head join/widen keeps the cell's VLA frame | make `widen_join` materialise mixed-origin pairs through `to_plain` | pin FAILs: the read-back origin is demoted |
