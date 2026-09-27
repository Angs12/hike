# Pins: Hike_origin

Module `hike_origin` (`src/hike_origin/hike_origin.ml`).
One row per pin in `test/unit/test_hike_origin.ml`.

The module is the origin leaf library: the ADT and its per-origin facts
table.  Red evidence is by review: each disable recipe is the textual
inversion of the pinned branch, and the pin's exact-equality assertion
fails under that inversion.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| ORI-01 | `facts Stack`: base = `segment_base` (2^62+8), certified 4, ±8 MiB clamps; the VLA band below its anchor, disjoint from the window side | change `facts Stack`'s `base` to `0L` | pin FAILs: the base assert fails |
| ORI-02 | the ADT is total: five constructors, each with a name | drop a constructor from the `name` match | pin FAILs: the name assert fails (inexhaustible match) |
| ORI-03 | `origin`: a stack value reads `Some Stack`; a plain singleton, an absolute Clp, and a stack∪plain union read `None` | make `origin` answer `Some Abs` for `Clp _` | pin FAILs: the plain/absolute asserts fail |
| ORI-04 | same-origin ops keep the origin: union/meet of two stack values read `Some Stack` | make `union`'s same-origin arm materialise via `to_plain` | pin FAILs: the union assert fails |
| ORI-05 | `refine_origin`: a wholly window-side value (offsets ≥ word) refines to `Window`, a wholly VLA-band value to `Vla`, a value spanning the entry line keeps `Stack`, plain passes through | swap the two band comparisons in `refine_origin` | pin FAILs: the window/vla/crossing asserts fail |
| ORI-06 | the per-def origin stamp: a solved sub's window-side address def (`rsp+16`) reads `Some Window` through `Vsa.Def_origin.def_origin` | make `stamp_origin` stamp `Some Abs` unconditionally | pin FAILs: the stamped origin assert fails |
