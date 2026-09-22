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
| ENV-02 | `Vsa.set_env_tag` stores the env on the def value; `env_tag` reads it back (`AI.equal` round-trip). | Make `set_env_tag env d = d` (l.476). | ENV-02; also ENV-03..09, ENV-12, ENV-14, ENV-15. |
| ENV-03 | The stored payload is the same physical `AI.t` (`Some env`, no copy). | In `set_env_tag`, store a rebuilt-but-`AI.equal` copy of `env` instead of `Some env`. | ENV-03 (`Base.phys_equal` false); ENV-02 still passes. |
| ENV-04 | The tag rides the def's KB value, so `Def.with_rhs` keeps it. | `set_env_tag env d = d` (value slot never populated). | ENV-04. |
| ENV-05 | `Term.map def_t` rebuilds the def without dropping its KB value. | `set_env_tag env d = d`. | ENV-05. |
| ENV-06 | `stamp_envs_of_sol` tags each def with its own before-state; the first def's tag is the block pre. | `set_env_tag env d = d`. | ENV-06. |
| ENV-07 | The sweep advances `env := denote_def d env`, so a def's tag is the prior transfer's product. | In `stamp_envs_of_sol`, stamp every def with the block `pre` (`set_env_tag pre d`). | ENV-07 (tag is `pre`, expected the first product). |
| ENV-08 | The block post is the last def's tag advanced once more through `denote_def`. | In `stamp_envs_of_sol`, do not advance `env` across defs (stamp all with `pre`). | ENV-08. |
| ENV-09 | `denote_exp_at` evaluates a tagged def in its tag env (memory-bearing query). | In `denote_exp_at`, ignore the tag: `let env = AI.top` (l.588-590). | ENV-09 (top, not `{7}`). |
| ENV-10 | A tagless def denotes TOP even when the block pre binds the queried var. | In `denote_exp_at`, a missing tag falls back to `pre` instead of `AI.top`. | ENV-10 (`pre` binds `x = {5}`). |
| ENV-11 | `denote_exp_at` with no def evaluates in the block post. | In `denote_exp_at`'s `None` arm, use `pre` instead of `post` (l.586). | ENV-11 (`{1}` instead of `{2}`). |
| ENV-12 | The tag answer equals the raw `solve_denote` replay on a multi-def block (0 mismatches). | Ignore the tag in `denote_exp_at` (`let env = AI.top`). | ENV-12 (`facts.denote` top vs raw replay). |
| ENV-13 | `Hike.Promote.rewrite_program` rewrites a surviving def's rhs. | In `src/hike_promote.ml`, make the rewrite return the prog unchanged. | ENV-13 (rhs equal); ENV-16/17 also lose the minted arg. |
| ENV-14 | The promote rewrite preserves mapped defs' tags (values survive the map). | Rebuild surviving defs with `Def.create` (drop the KB value) instead of a value-preserving map. | ENV-14; also ENV-15. |
| ENV-15 | The seam answers a rewritten mapped def from its tag. | Ignore the tag in `denote_exp_at` (`let env = AI.top`). | ENV-15 (top, not `{7}`). |
| ENV-16 | A freshly minted `hike_argN` def carries no tag. | In `src/hike_promote.ml`, stamp each minted `hike_argN` def with `Vsa.set_env_tag`. | ENV-16 (`is_none` false). |
| ENV-17 | A minted def denotes TOP through the seam. | In `denote_exp_at`, a missing tag falls back to `pre` instead of `AI.top`. | ENV-10 always; ENV-17 when the block pre binds the minted arg lhs. |
