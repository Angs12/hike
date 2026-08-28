# 12: create_native_fp_call binds every consumer-width view

**What to build:** At the FP call block, resolve x-operands from the most-recent in-block `intrinsic:xN_*` def (binding width varies per entry: CVTSI642SS → u64, CVTSS2SD → u32) and bind every consumer-width view of the result (y0_64/y0_32/y0_1), so all consumers read the right width. Completes the corrected BAP FP modeling (width-homogeneous lanes).

**Blocked by:** T11 (rename_intrinsics width-suffix canonicalization (hike.ml)).

**Status:** ready-for-agent

- [ ] Doubles exact (e.g. `div.c` prints `nc=128.750000 dnc=128.750000`)
- [ ] Doubles exact at the printf boundary (`bits=4008000000000000` = 3.0)
- [ ] No i32 coercion of an i64 SD result
