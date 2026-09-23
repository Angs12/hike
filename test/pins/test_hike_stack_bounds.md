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
| HSB-01 | `i64_opt`: a width-64 word is representable; a high bit reads signed (`ones 64 → -1`) | change `Ok v -> Some v` to `_ -> None` in `i64_opt` | pin FAILs: `i64_opt (w64 5)` becomes `None` |
| HSB-02 | `i64_opt`: a value past 2^64-1 is `None` | change `Error _ -> None` to `Error _ -> Some 0L` in `i64_opt` | pin FAILs: `i64_opt (ones 65)` becomes `Some 0L` |
| HSB-03 | `position_pair`: representable offsets map to `base + offset` | replace the two `position_of_offset` binds with `Some lo`/`Some hi` | pin FAILs: bounded offsets return raw offsets, not positions |
| HSB-04 | `position_pair`: an unrepresentable endpoint yields `None` | make `i64_opt` total (`Error _ -> Some 0L`) | pin FAILs: the `ones 65` endpoint no longer aborts the bind |
| HSB-05 | `position_pair`: a positive offset whose position overflows yields `None` | delete the `o > 0 && r < o` test in `position_of_offset` | pin FAILs: `0x4000000000000000` position returns `Some` |
| HSB-06 | `stack_floor ~entry = entry + Int64.min_int` (the below-entry bound) | change `Stdlib.Int64.min_int` to `Stdlib.Int64.max_int` | pin FAILs: the concrete constant `-4611686018427387896` changes |
| HSB-07 | `args_ceiling = Int64.max_int` | change the literal to `Stdlib.Int64.min_int` | pin FAILs: `args_ceiling` no longer equals `max_int` |
| HSB-08 | `positions_of_offsets`: a finite offset interval projects to exact positions | swap `~f:position_pair` for a constant `Some (0L, 0L)` | pin FAILs: bounds become `(0,0)`, not `base-16, base-8` |
| HSB-09 | `positions_of_offsets`: a plain set (`offset_extrema = None`) yields `None` | make `offset_extrema` return `Some (zero, ones)` for non-stack values | pin FAILs: plain sets now answer positions |
| HSB-10 | `positions_of_offsets`: an offset word wider than int64 yields `None` | make `position_pair` ignore `i64_opt` (`Some (lo, hi)`) | pin FAILs: a width-65 offset no longer aborts |
| HSB-11 | `positions_of_offsets`: an offset whose position overflows yields `None` | delete the overflow test in `position_of_offset` | pin FAILs: the `2^62` offset gets a wrapped position |
| HSB-12 | `unsigned_bounds`: plain extrema as int64; a stack value projects absolutely | return `(Ws.offset_extrema …)`'s raw words instead of `min_elem`/`max_elem` | pin FAILs: the stack case answers offsets (`-8`), not positions |
| HSB-13 | `unsigned_bounds`: an empty set (`min_elem = None`) yields `None` | default the missing extremum to `Some (zero 64)` | pin FAILs: the bottom set answers `Some` |
| HSB-14 | `unsigned_bounds`: an extremum past int64 yields `None` | make `i64_opt` total (`Error _ -> Some 0L`) | pin FAILs: the width-65 extremum no longer aborts |
| HSB-15 | `full_bounds`: a swapped hull spans the whole scope | drop the `lo > hi` arm (fall through to the direction tests) | pin FAILs: `(10, -10)` no longer returns `(flo, cei)` |
| HSB-16 | `full_bounds`: an ascending set reaches `cei`, keeping `lo` | drop the `is_ascending` arm | pin FAILs: the ascending case returns `(flo, cei)` |
| HSB-17 | `full_bounds`: a descending set reaches `flo`, keeping `hi` | drop the `is_descending` arm | pin FAILs: the descending case returns `(flo, cei)` |
| HSB-18 | `full_bounds`: a finite or circular set spans the whole scope | make the fallthrough return `(lo, hi)` | pin FAILs: the finite/circular case returns the passed hull |
| HSB-19 | `escape_extent`: a plain value (no `stack_offsets`) yields `None` | return `Some (floor, args_ceiling)` in the `None` arm of `stack_offsets` | pin FAILs: plain sets now answer a scope hull |
| HSB-20 | `escape_extent`: a finite stack value keeps its exact positions | route `Some (lo, hi)` through `full_bounds` unconditionally | pin FAILs: a finite hull gets widened to a scope bound |
| HSB-21 | `escape_extent`: unrepresentable positions become the whole scope | change the `positions_of_offsets = None` arm to `None` | pin FAILs: the width-65 offset no longer returns `(floor, cei)` |
| HSB-22 | `escape_extent`: a descending stack value reaches the floor | drop the `is_infinite …` guard so `Some (lo, hi)` returns directly | pin FAILs: the descending hull stays `(base, base+100)` |
| HSB-23 | `escape_extent`: a top stack value spans the whole scope | hardcode the `is_infinite` branch to `Some (lo, hi)` | pin FAILs: top returns its swapped `(base, base-1)` hull |
| HSB-24 | `escape_extent`: an ascending stack value's signed max wraps to the whole scope | make `full_bounds` skip the `lo > hi` arm | pin FAILs: the wrapped ascending hull is not `(floor, cei)` |
| HSB-25 | `key_extent`: a finite stack value keeps its exact offset extrema | return `(zero, ones)` for the finite `stack_offsets` arm | pin FAILs: `-8` becomes the full key line |
| HSB-26 | `key_extent`: an ascending stack value clamps the top to `ones` | drop the `is_ascending` arm of `clamp` | pin FAILs: an ascending value returns `(lo, hi)` |
| HSB-27 | `key_extent`: a descending stack value clamps the bottom to `zero` | drop the `is_descending` arm of `clamp` | pin FAILs: a descending value returns `(lo, hi)` |
| HSB-28 | `key_extent`: a circular (top) value spans the key line | drop the `is_circular` arm of `clamp` | pin FAILs: a top value returns `(lo, hi)` |
| HSB-29 | `key_extent`: an empty stack value (`min_elem = None`) spans the key line | change the `_ -> Some (zero, ones)` fallback to `None` | pin FAILs: a bottom stack value answers `None` |
| HSB-30 | `key_extent`: a plain in-band set clamps its own segment-relative hull | make `stack_bounds` return the raw words, not `offset`-relative | pin FAILs: `(0,16)` becomes `(base, base+16)` |
| HSB-31 | `key_extent`: a plain out-of-band set keeps its own word extrema | return `Some (zero, ones)` in the final `min_elem/max_elem` arm | pin FAILs: `(1,2)` becomes the full key line |
| HSB-32 | `key_extent`: a plain empty set yields `None` | default the final `min_elem/max_elem` `None` to `Some (zero, ones)` | pin FAILs: a bottom plain set answers `Some` |
| HSB-33 | `key_extent`: an offset word wider than int64 is preserved, not dropped | replace `clamp lo hi` with an `i64_opt`-gated branch that returns `None` on error | pin FAILs: a width-65 offset answers `None` |
| HSB-34 | `caller_window_bytes = 65536L` | change the literal | pin FAILs: the capacity constant changes |
| HSB-35 | `stack_max = 65536L` | change the literal | pin FAILs: the below-entry clamp changes |
