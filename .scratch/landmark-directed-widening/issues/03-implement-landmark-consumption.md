# 03: Implement landmark consumption (lm_calc_steps + selective_widen_extrapolate + current_lm_head)

**What to build:** The "consumption" half of Simon & King: given the accumulated landmark environment and the current WTO head, compute the Listing-4 1-D extrapolation step (the stable-bound progression) that widening should apply. This is the math that turns acquired boundaries into a directed widen.

**Blocked by:** T01 (Recover cbat_landmarks.ml (compiling API surface)).

**Status:** ready-for-agent

- [ ] `lm_calc_steps` consumes `landmark_env` + `current_lm_head` and yields an extrapolation delta
- [ ] `selective_widen_extrapolate` matches Listing 4 of Simon & King for a 1-D progression (stable bounds, no over-widening)
- [ ] Standalone test: a monotone 1-D sequence converges to the landmark-stable bound
