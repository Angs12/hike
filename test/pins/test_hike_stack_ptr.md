# Pins: Hike_stack_ptr

Module `src/hike_stack_ptr.ml` (interface `src/hike_stack_ptr.mli`).
One row per pin in `test/unit/test_hike_stack_ptr.ml` (ids `SPTR-01`..`SPTR-04`).

The module is the one home of the stack storage and its addresses: one LLVM
alloca per layout region, the region's mem var, and the range's
entry-relative base.  The pins call `build` against a real
`Llvm.create_context` + `create_builder` (positioned at a function entry,
the emitter's `create_sub` position) and inspect both the returned storage
record and the printed module.

Red evidence is by review: each disable recipe is the textual inversion of
the pinned branch in `hike_stack_ptr.ml`, and the pin's exact assertion
fails under that inversion.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| SPTR-01 | `build` maps `layout.regions` one-to-one: an empty layout yields `[]` and emits no alloca. | In `src/hike_stack_ptr.ml` `build`, special-case `[]` to return one dummy storage (or seed a default region). | SPTR-01 FAILs: the list is nonempty and/or the IR contains `alloca`. |
| SPTR-02 | One region becomes one storage: `mem = Model.region_mem id`, `rel = lo - segment_base` (signed entry-relative), a real `[16 x i8]` alloca named `stack_r3` at alignment 16. | In `build`, replace `{ mem = Model.region_mem id; …; rel = Int64.sub lo Model.segment_base }` with a fixed mem/`rel = 0L`, or drop `Llvm.set_alignment 16`. | SPTR-02 FAILs: a storage does not carry the region's mem var / its `-24` rel, or the name/align/extent no longer match. |
| SPTR-03 | Storages follow layout order; each `rel` is its range's signed entry-relative base (a below-entry range is negative, an above-entry range positive), and each alloca carries the region's exact byte extent. | In `build`, sort the regions descending, or return `rel = lo` (absolute) instead of `lo - segment_base`. | SPTR-03 FAILs: the mem-var/order/rel correspondence breaks, or the `-16`/`64` rel witnesses vanish. |
| SPTR-04 | An over-bound byte request (`>= 0x7fff_fff0`) is clamped loudly to the array-count bound and still builds the alloca. | In `build`, drop the `Hike_diag.warn` (clamp silently), or remove the clamp (let `Int64.to_int` truncate). | SPTR-04 FAILs: the stderr capture loses `clamped`, or the emitted extent is not `[2147483632 x i8]`. |
