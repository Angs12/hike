# 02 — Restriction removal + VSA self-seeding (the semantic core)

**Status:** ready-for-agent
**Depends on:** 01 (the baseline must exist before the tree changes)
**Blocks:** 03

**What to build:** the whole semantic change of the spec
(`.scratch/restriction-removal/spec.md` §2.1, §2.2, §2.3; the file:line
inventory in §3 is against `5ae223b` — re-locate by name, the fusion has moved
lines): the relevance pass is deleted, the fixpoint denotes EVERY def, and
stack accesses are seeded by the VSA itself (the two-channel frame-residency
proof) instead of the `stack_access` tag. `vsa_info` becomes the only carrier
of stack-access-ness.

READ FIRST: the spec (all of §1–§3 — it is a verified fact base with a
complete inventory); ADR `docs/adr/0003-remove-restriction-vsa-seeding.md`;
the implementation notes `/tmp/opencode/single-pass-trace-partitioning/implementation-notes.md`
(the code map; plus this spec's own line references).

The semantic inventory (this ticket; the mechanical signature sweep is
ticket 03):
- [ ] `src/hike_vsa_relevance.ml` DELETED except `detect_dynamic_alloc`,
      which relocates (unchanged) into `cbat_vsa` (exported; the hike-vsa
      pass calls it once per sub). `dynamic_alloc` tag deleted; the
      `vla_bounds` walks in `hike_vsa.ml` receive the tid set directly.
- [ ] The `hike-relevance` pass registration deleted (`src/hike.ml`);
      `hike-vsa`'s dep becomes `hike-filter`.
- [ ] `denote_def`'s tag gate DELETED — every def is denoted;
      `apply_frame_def_list`'s gate (`:319`) deleted.
- [ ] The backward-lane gates DELETED: `meet_var`'s refineable check
      (`:1032`), `constrain_cell`'s free-vars gate (`:1041`), and the
      `refineable` PRODUCTION (`refineable_of_sub` `:2704`) — callers pass
      None/empty (ticket 03 sweeps the signatures; do not churn them here).
      The Phase B `tag_relevant` pruning (`:2316-2329`) is deleted here IF it
      still exists (spec 1's ticket 02 may already have removed it).
- [ ] The two-channel seeding in `Hike_vsa.offsets_of_sub`'s per-def walk:
      Channel 1 (direct) = `rewrite_addr` succeeds on the pre-def state
      (widened frame-affine addresses still seed; `Infinite` stays live);
      Channel 2 (reloaded) = `rewrite_addr` fails → denote the WHOLE address
      in the pre-def state → seed IFF the value set is BOUNDED and a SUBSET
      of the frame neighborhood `[−64 KiB, +64 KiB]` around the origin.
      **SUBSET, never intersection — non-seeding is the sound fallback**
      (§2.2's non-negotiable invariant). Walk EVERY def (drop the
      `last_tagged` cut).
- [ ] `has_stack_access_tags` skip gate → the has-any-Load/Store prefilter
      (§2.2); `has_relevant_tags`/re-analyze guard deleted.
- [ ] `stack_access` tag deleted; `bil2llvm.ml`'s `is_stack_access`
      redefined as "the def carries ANY `vsa_info` tag" (the 100% invariant
      becomes structural; keep the poison path for `Dead`).
- [ ] `compute_need`'s relevant filter (`:2838`) → track every def in the
      SCC's value-flow cycle.
- [ ] Tests migrated: `tag_all` (`:1090`) deleted; manual `stack_access`
      fixtures (`:5576, :6404`) rewritten to seedable shapes or deleted with
      each flagged in the report (test bugs, not spec concessions); the
      strict F1-NEQ check stays green.
- [ ] `dead?` `offsets_from_partitioned` in `hike_vsa.ml` — verify; migrate
      or delete per the spec (§2.2).

Gates (all must pass; precision expectations per §2.4):
- [ ] `dune runtest` 0 FAIL (incl. strict F1-NEQ).
- [ ] Fresh plugin install (`.mli` may change → `bapbuild -clean && make`
      if needed); `run_corpus.sh` 32/32 rc=0 (0-failed on
      `check_allocas.sh`; counts may RISE — more tagged defs);
- [ ] `run_semantic_all.sh` ≥ 29 PASS / 3 known FAIL, 0 SKIP; `run_semantic.sh` 8/8.
- [ ] corpus_watch + precision_probe over the full corpus: 0 crashes;
      exactness moves UP (§2.4 anchors: rec_struct 96.77%, variadic 100.00%,
      sret_big 82.50%); the saved-address class (variadic's
      `RAX := mem[RBP-0xC8]; mem[RAX]`) expected to shift `Unbounded` →
      `Range`/`Infinite`.
- [ ] No debug prints in production; comments cite the spec sections.

Gate: the full battery + the §2.4 precision expectations recorded in the report.
