# 09: Remove the threshold ladder (no fallback)

**What to build:** `cbat_thresholds.ml` and every `selective_widen_join_threshold` call site are deleted; landmark-directed widening is the only extrapolation path, with no toggle back to thresholds. Per the user directive there is no threshold fallback — thresholds are removed entirely, not demoted.

**Blocked by:** T08 (Wire consumption at the widening point (cbat_vsa.ml)).

**Status:** ready-for-agent

- [ ] `cbat_thresholds.ml` absent; `grep` for `selective_widen_join_threshold` / `cbat_thresholds` returns nothing in source
- [ ] `dune build` green
- [ ] Coreutils still 93/93 at this stage (verified by `scripts/coreutils_pipeline.sh`)
