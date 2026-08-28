# 07: Implement Clp.widen_join as Listing-4 1-D extrapolation

**What to build:** The CLP widening join becomes the faithful Simon & King Listing-4 extrapolation over 1-D progressions, consuming the landmark env. This is the concrete extrapolation operator the widening point will call.

**Blocked by:** T03 (Implement landmark consumption (lm_calc_steps + selective_widen_extrapolate + current_lm_head)), T06 (Add landmark types to cbat_ai_representation + cbat_refinement).

**Status:** ready-for-agent

- [ ] `Clp.widen_join` applies the Listing-4 step on a 1-D progression and stabilizes
- [ ] A unit test on a 1-D increasing sequence converges to the landmark-stable bound, not top
