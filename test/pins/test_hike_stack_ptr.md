# Pins: Hike_stack_ptr

Module `src/hike_core/hike_stack_ptr.ml` (interface `src/hike_core/hike_stack_ptr.mli`).
One row per pin in `test/unit/test_hike_stack_ptr.ml` (ids `SPTR-02`, `SPTR-04`..`SPTR-06`).

The module is the one home of the stack storage and its addresses: one LLVM
alloca per layout region, the region's mem var, and the range's
entry-relative base.  The pins call `build_frame` against a real
`Llvm.create_context` + `create_builder` (positioned at a function entry,
the emitter's `create_sub` position) and inspect both the returned storage
record and the printed module.

Red evidence is by review: each disable recipe is the textual inversion of
the pinned branch in `hike_stack_ptr.ml`, and the pin's exact assertion
fails under that inversion.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| SPTR-02 | One region becomes one storage: `mem = Model.region_mem id`, `rel = lo - segment_base` (signed entry-relative), a real `[16 x i8]` alloca named `stack_r3` at alignment 16. | In `build_frame`, replace `{ mem = Model.region_mem id; …; rel = Int64.sub lo Model.segment_base }` with a fixed mem/`rel = 0L`, or drop `Llvm.set_alignment 16`. | SPTR-02 FAILs: a storage does not carry the region's mem var / its `-24` rel, or the name/align/extent no longer match. |
| SPTR-04 | A runtime layout's residue base is a GEP chain off the entry call (`rstack_top`, `rstack_entry = top - (align16(window) + word)`), a carved region stays an alloca, and the helpers are weak noinline definitions carrying `noalias`, `nocapture` and `memory(inaccessiblemem: write)`. | Emit an alloca for the residue, or drop an attribute in `define_enter` / `define_set`. | SPTR-04 FAILs: the IR text lacks the chain or the attributes. |
| SPTR-05 | A bounded layout builds no runtime helper (`hike_rstack` is absent from the module). | Define the helpers in every module. | SPTR-05 FAILs: the helper text appears. |
| SPTR-06 | Under `opt-21 -O2` the frame is a fresh object: a frame store survives an unknown call and a store through an argument (the load folds to 42), and the frame is never an argument. Fails when `opt-21` is absent. | Make the frame an argument, or drop `noalias` / `nocapture` / the `memory` attribute. | SPTR-06 FAILs: a `load i64` survives. |
