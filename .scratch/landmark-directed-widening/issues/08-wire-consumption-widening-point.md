# 08: Wire consumption at the widening point (cbat_vsa.ml)

**What to build:** At WTO heads in the fixpoint widening, call `lm_calc_steps` → `selective_widen_extrapolate` so widening is landmark-directed. Loops still terminate and the analysis stays sound; this is the moment landmark-directed widening actually drives the fixpoint (replacing threshold widening's role).

**Blocked by:** T05 (Wire acquisition: observe_unsat in meet_var on empty meet), T07 (Implement Clp.widen_join as Listing-4 1-D extrapolation).

**Status:** ready-for-agent

- [ ] Loops that previously needed threshold widening now terminate via landmarks
- [ ] An external-behavior test shows the correct loop-bound fixpoint value
- [ ] No unsound over-approximation introduced
