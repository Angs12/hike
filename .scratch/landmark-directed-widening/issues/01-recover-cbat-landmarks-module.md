# 01: Recover cbat_landmarks.ml (compiling API surface)

**What to build:** A new landmark-directed widening module that compiles against the current VSA types and exposes the full API the fixpoint will call: a landmark environment, the unsat-boundary observer, WTO-head discovery, the consumption step, the Listing-4 extrapolation, and the current-head tracker. The pi session `01a03eb4` carried the original implementation (with a compile error at line 131); replay those edit patches onto `recover-golden` first. If they do not apply or do not compile even after fixing line 131, re-implement the module from `AGENTS.md` §Widening, `.slim/deepwork/not-yet-landed.md`, ADR 0002, and the Simon & King paper — do NOT substitute thresholds.

**Blocked by:** None (can start immediately).

**Status:** ready-for-agent

- [ ] `src/cbat_vsa/cbat_landmarks.ml` (and `.mli` if needed) compiles under `dune build`
- [ ] The module exposes `landmark_env`, `observe_unsat`, `heads_of_wto`, `lm_calc_steps`, `selective_widen_extrapolate`, `current_lm_head` with signatures consistent with the current `cbat_vsa`/`cbat_clp` types
- [ ] No `cbat_thresholds` dependency is introduced
