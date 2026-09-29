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
| ORI-05 | the boundary refinement: a wholly window-side value (offsets ≥ word) refines to `Window`; a Vla-frame value keeps its frame whatever its offsets (the routing gate decides routability at the stamp); a value spanning the entry line keeps `Stack`; plain passes through | make `refine_origin` re-absorb a `Vla` value onto `Stack` | pin FAILs: the keeps-its-frame assert fails |
| ORI-07 | the store→load round-trip (frame): the load's stamped ADDRESS origin (a frame cell) is `Some Stack` | make `stamp_origin` use the loaded value for a load instead of the address | pin FAILs: the read-back origin is `Some Abs`/the value's |
| ORI-09 | the VLA seed: `rsp := rsp − rax` with a set-valued size stamps the decrement def's value `Vla T` (T = its own tid) as the frame base (`Rel (Vla T, {0})`, materialised to the base range) and records `{off_lo = 0; off_hi = Some 32; base_lo = Some −48; base_hi = Some −32}` | make `vla_seed` return `p` (no seed) | pin FAILs: the stamp, the base-range, and the extent asserts fail |
| ORI-17 | the D1 shape predicate (`vla_event`): a singleton amount is not an event; a TOP size and a directional-infinite size are events with `off_hi = None` | make `vla_event` require a bounded amount | pin FAILs: the TOP/infinite accepts fail |
| ORI-18 | the D10 namespace test (`names_stack_line`): `Stack`, `Window` and a `Vla` frame name the stack line; `Abs` and `Rip` name none | make `names_stack_line` answer `true` for `Abs` | pin FAILs: the absolute-origin assert fails |
