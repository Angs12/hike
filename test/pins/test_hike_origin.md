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
| ORI-05 | the boundary refinement: a wholly window-side value (offsets ≥ word) refines to `Window`; a Vla-frame value keeps its frame whatever its offsets (the routing gate decides routability at the stamp); a value spanning the entry line keeps `Stack`; plain passes through | make `refine_origin` re-absorb a `Vla` value onto `Stack` | pin FAILs: the keeps-its-frame assert fails |
| ORI-06 | the per-def origin stamp: a solved sub's window-side address def (`rsp+16`) reads `Some Window` through `Vsa.Def_origin.def_origin` | make `stamp_origin` stamp `Some Abs` unconditionally | pin FAILs: the stamped origin assert fails |
| ORI-07 | the store→load round-trip (frame): the load's stamped ADDRESS origin (a frame cell) is `Some Stack` | make `stamp_origin` use the loaded value for a load instead of the address | pin FAILs: the read-back origin is `Some Abs`/the value's |
| ORI-08 | the store→load round-trip (window): the load's stamped address origin (`rsp+16`, refined) is `Some Window` | drop the address refinement in `stamp_origin`, or drop `refine_origin`'s `Stack→Window` arm | pin FAILs: the read-back origin is `Some Stack` |
| ORI-09 | the VLA seed: `rsp := rsp − rax` with a set-valued size stamps the decrement def's value `Vla T` (T = its own tid) as the frame base (`Rel (Vla T, {0})`, materialised to the base range) and records `{off_lo = 0; off_hi = Some 32; base_lo = Some −48; base_hi = Some −32}` | make `vla_seed` return `p` (no seed) | pin FAILs: the stamp, the base-range, and the extent asserts fail |
| ORI-10 | +INT inside the extent shifts the frame-relative offset exactly and keeps the frame (the materialised range shifts) | drop the `Add`/`Sub` wrap rows for a `Vla` operand | pin FAILs: both keeps-the-frame asserts fail |
| ORI-11 | a value crossing below the gate is refused at the origin stamp (`Abs`); the frame-relative value keeps its raw `Vla` origin and materialises | make `routable_origin` answer `Some (Vla _)` out of gate | pin FAILs: the stamps-Abs assert fails |
| ORI-12 | same-frame unions stay exact (`Wrap (Vla t)`); different-frame unions materialise (the cross-line absorb excludes Vla∪Vla) | make `cross_line` absorb `Vla ∪ Vla` too | pin FAILs: the different-frame assert fails |
| ORI-13 | a Vla value unioned with an entry-line value materialises through its base range (no single origin), the runs stay exact | make the cross-line rule absorb `Vla ∪ Stack` onto `Stack` | pin FAILs: the no-single-origin assert fails |
| ORI-14 | the store→load round-trip (VLA): a stored VLA-frame pointer's VALUE reads back `Some (Vla T)` with the same tid | restore the load fold's `WordSet.bottom` seed | pin FAILs: the read-back value origin demotes |
| ORI-15 | the round-trip across a machine call: the saved pointer VALUE survives the call keep (the VLA-frame SP keeps from its extent's low end) | make `frame_keep` use the plain max-offset boundary for Vla SPs too | pin FAILs: the read-back origin is demoted |
| ORI-16 | the round-trip across a loop: the loop-head join/widen keeps the cell's VLA frame | make `widen_join` materialise mixed-origin pairs through `to_plain` | pin FAILs: the read-back origin is demoted |
| ORI-17 | the D1 shape predicate (`vla_event`): a singleton amount is not an event; a TOP size and a directional-infinite size are events with `off_hi = None` | make `vla_event` require a bounded amount | pin FAILs: the TOP/infinite accepts fail |
| ORI-18 | the D10 namespace test (`names_stack_line`): `Stack`, `Window` and a `Vla` frame name the stack line; `Abs` and `Rip` name none | make `names_stack_line` answer `true` for `Abs` | pin FAILs: the absolute-origin assert fails |
