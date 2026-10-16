# Pins: Hike_stack_bounds

Module `hike_stack_bounds` (`src/hike_stack_bounds/hike_stack_bounds.ml`).
One row per pin in `test/unit/test_hike_stack_bounds.ml`.

The module is a thin pure seam over `Cbat_clp_set_composite` / `Cbat_word`
/ `Cbat_clp`; the pins drive every documented branch (exact, boundary,
doubt). Red evidence is by review: each disable recipe is the textual
inversion of the pinned branch in `hike_stack_bounds.ml`, and the pin's
exact-equality assertion fails under that inversion.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| HSB-03 | `position_pair`: representable offsets map to `base + offset` | replace the two `position_of_offset` binds with `Some lo`/`Some hi` | pin FAILs: bounded offsets return raw offsets, not positions |
| HSB-06 | `stack_floor ~entry = entry + Int64.min_int` (the below-entry bound) | change `Stdlib.Int64.min_int` to `Stdlib.Int64.max_int` | pin FAILs: the concrete constant `-4611686018427387896` changes |
| HSB-08 | `positions_of_offsets`: a finite offset interval projects to exact positions | swap `~f:position_pair` for a constant `Some (0L, 0L)` | pin FAILs: bounds become `(0,0)`, not `base-16, base-8` |
| HSB-12 | `unsigned_bounds`: plain extrema as int64; a stack value projects absolutely | return `(Ws.offset_extrema …)`'s raw words instead of `min_elem`/`max_elem` | pin FAILs: the stack case answers offsets (`-8`), not positions |
| HSB-15 | `full_bounds`: a swapped hull spans the whole scope | drop the `lo > hi` arm (fall through to the direction tests) | pin FAILs: `(10, -10)` no longer returns `(flo, cei)` |
| HSB-19 | `escape_extent`: a plain value (no `stack_offsets`) yields `None` | return `Some (floor, args_ceiling)` in the `None` arm of `stack_offsets` | pin FAILs: plain sets now answer a scope hull |
| HSB-25 | `key_extent`: a finite stack value keeps its exact offset extrema | return `(zero, ones)` for the finite `stack_offsets` arm | pin FAILs: `-8` becomes the full key line |
| HSB-34 | `caller_window_bytes = 65536L` | change the literal | pin FAILs: the capacity constant changes |
