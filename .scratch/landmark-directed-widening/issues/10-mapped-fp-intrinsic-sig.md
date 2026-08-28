# 10: mapped_fp_intrinsic + sub-sig synthesis (hike.ml)

**What to build:** BAP expands only the core soft-float names into bodies; the cast/convert classes arrive as body-less intrinsic stubs. Classify them by the emitter's mapping (`mapped_fp_intrinsic`) rather than body presence, and synthesize their model interface by arity, so FP *use* is present for casts/conversions. This restores FP presence that was lost from source.

**Blocked by:** None (can start immediately).

**Status:** ready-for-agent

- [ ] Body-less cast/convert classes (`cast_sfloat_*`/`cast_float_*`/`cast_sint_*`/`fconvert_*`) are kept as `intrinsic:*` subs
- [ ] `compute_sub_sig` yields an arity-correct sig (binops [x0;x1], casts [x0]; rets [y0]; u64), sig-matched to the working body-ful models
- [ ] No arg/ret misbinding (arg0 no longer evaluated as RDI; `create_native_fp_call` no longer silently discards the computed result)
