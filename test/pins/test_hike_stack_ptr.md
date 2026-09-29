# Pins: Hike_stack_ptr

Module `src/hike_stack_ptr.ml` (interface `src/hike_stack_ptr.mli`).
One row per pin in `test/unit/test_hike_stack_ptr.ml` (ids `SPTR-01`..`SPTR-03`).

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
| SPTR-02 | One region becomes one storage: `mem = Model.region_mem id`, `rel = lo - segment_base` (signed entry-relative), a real `[16 x i8]` alloca named `stack_r3` at alignment 16. | In `build`, replace `{ mem = Model.region_mem id; …; rel = Int64.sub lo Model.segment_base }` with a fixed mem/`rel = 0L`, or drop `Llvm.set_alignment 16`. | SPTR-02 FAILs: a storage does not carry the region's mem var / its `-24` rel, or the name/align/extent no longer match. |
