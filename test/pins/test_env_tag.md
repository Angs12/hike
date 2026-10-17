# test_env_tag pins

Module `test/unit/test_env_tag.ml` (ids `ENV-01`..`ENV-17`), migrating
`test_cbat/test_env_tag.ml`.  Every source `check` site is carried as one
pin; none retired.  Mechanism: the Env Tag (KB value slot `hike-env-tag`
on each def, stamped by `Cbat_vsa.stamp_envs_of_sol`) and the gate-free
denotation seam `Cbat_vsa.denote_exp_at` / `Hike.Kb.facts.denote`.

The Env Tag mechanism is not Test_seam-switchable, so — per the lane
spec `§Fail-before` — the disable recipes below are textual and the red is
re-demonstrated by review when the mechanism changes.  Each recipe names
the pins it turns red; no measured red is claimed here.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| ENV-01 | `Vsa.env_tag` returns `None` for a def outside the analysis boundary (slot absent). | In `src/cbat_vsa/cbat_vsa.ml`, make `env_tag` return `Some AI.top` unconditionally (l.473). | ENV-01 (expects `None`). |
| ENV-06 | `stamp_envs_of_sol` tags each def with its own before-state; the first def's tag is the block pre. | `set_env_tag env d = d`. | ENV-06. |
| ENV-07 | The sweep advances `env := denote_def d env`, so a def's tag is the prior transfer's product. | In `stamp_envs_of_sol`, stamp every def with the block `pre` (`set_env_tag pre d`). | ENV-07 (tag is `pre`, expected the first product). |
| ENV-09 | `denote_exp_at` evaluates a tagged def in its tag env (memory-bearing query). | In `denote_exp_at`, ignore the tag: `let env = AI.top` (l.588-590). | ENV-09 (top, not `{7}`). |
| ENV-10 | A tagless def denotes TOP even when the block pre binds the queried var. | In `denote_exp_at`, a missing tag falls back to `pre` instead of `AI.top`. | ENV-10 (`pre` binds `x = {5}`). |
| ENV-11 | `denote_exp_at` with no def evaluates in the block post. | In `denote_exp_at`'s `None` arm, use `pre` instead of `post` (l.586). | ENV-11 (`{1}` instead of `{2}`). |
| ENV-13 | `Hike.Promote.rewrite_program` rewrites a surviving def's rhs. | In `src/hike_promote.ml`, make the rewrite return the prog unchanged. | ENV-13 (rhs equal); ENV-16/17 also lose the minted arg. |
| ENV-14 | The promote rewrite preserves mapped defs' tags (values survive the map). | Rebuild surviving defs with `Def.create` (drop the KB value) instead of a value-preserving map. | ENV-14; also ENV-15. |
| ENV-16 | A freshly minted `hike_argN` def carries no tag. | In `src/hike_promote.ml`, stamp each minted `hike_argN` def with `Vsa.set_env_tag`. | ENV-16 (`is_none` false). |
