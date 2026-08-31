# 03 — Dead-threading sweep + leftover plumbing (mechanical, no behavior change)

**Status:** ready-for-agent
**Depends on:** 02
**Blocks:** 04

**What to build:** the mechanical half the spec's §2.1 inventory holds back
from ticket 02: with the semantic change landed (nothing produces a
`refineable` set anymore), delete the dead parameter threading and leftover
tag plumbing. Behavior is byte-identical to 02.

- [ ] The `?refineable` threading deleted across `assume_jump_cond_with_group`
      / `assume_jump_cond` / `denote_jump` / `denote_block_with_stores` /
      `static_graph_vsa` (spec §3: `:2551-2763, 2928` at `5ae223b`);
      `refineable_var_of` (`:2094`, fix its inverted comment on the way out)
      deleted.
- [ ] The `relevant` tag definition deleted from `cbat_vsa_utils.ml` (`:47`);
      any remaining `Utils.relevant` / `Term.has_attr _ relevant` readers
      swept (grep the repo — including `test_cbat/`, `zz_scratch_probe/`).
- [ ] `test_cbat/corpus_watch.ml`'s `HIKE_VSA_RESTRICTION` toggle + its doc
      line deleted (the baseline-skip mode dies with the restriction).
- [ ] `docs/vsa-usage.md` §2's stale claims + the `restriction_enabled` refs
      + the stale test count corrected (AGENTS.md already flags these).
- [ ] No remaining reference to: `hike_vsa_relevance`, `relevant` (the tag),
      `stack_access` (the tag), `refineable`, `tag_all`,
      `HIKE_VSA_RESTRICTION` — anywhere in the repo.

Gates:
- [ ] `dune runtest` 0 FAIL; the corpus emission is BYTE-IDENTICAL to 02's
      (re-emit and diff — this ticket changes no behavior);
- [ ] `check_allocas.sh` identical counts; `run_semantic_all.sh` ≥ 29/3 + 0 SKIP.

Gate: byte-parity emission + zero remaining references.
