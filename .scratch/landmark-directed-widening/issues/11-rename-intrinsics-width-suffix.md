# 11: rename_intrinsics width-suffix canonicalization (hike.ml)

**What to build:** BAP vars are width-blind (keyed on name only), so same-name diff-width SSE interface temps collapsed into one lane and corrupted doubles (BUG C). Canonicalize every interface temp to its width-suffixed name — BAP's `sse-binary` now appends the result width, e.g. `fadd_rne_ieee754_binary_32` vs `_64` — so each width threads its own phi/lane and no lookup conflates lanes.

**Blocked by:** T10 (mapped_fp_intrinsic + sub-sig synthesis (hike.ml)).

**Status:** ready-for-agent

- [ ] `rename_intrinsics` maps each interface temp to its width-suffixed name
- [ ] Verify BAP emits width-suffixed intrinsic names (`native_fp_op` maps both suffixed and legacy); if not, surface that gap as a blocker rather than working around it
- [ ] No same-name diff-width lane conflation in emitted IR
