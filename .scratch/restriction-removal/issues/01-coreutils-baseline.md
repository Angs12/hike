# 01 — Coreutils baseline (measurement only, no code)

**Status:** ready-for-agent
**Depends on:** the single-pass trace-partitioning spec COMPLETE (its branch merged)
**Blocks:** 02

**What to build:** the pre-deletion cost record for the restriction-removal spec
(`.scratch/restriction-removal/spec.md` §5.1, "Baseline FIRST, before any
deletion lands"). Run the coreutils pipeline on the current (post-fusion) tree
and record per-sub wall time + the stage breakdown, so the post-removal
differential (ticket 04) has its comparison point. NO code changes whatsoever.

Acceptance criteria:
- [ ] `scripts/coreutils_pipeline.sh` run to completion on the current tree
      (the installed plugin matches the tree: `dune build @install && dune
      install && cd src && bapbuild -clean && make` — dune install FIRST,
      THEN bapbuild -clean: bapbuild links the INSTALLED hike.cbat_vsa, so a
      plain `make` after a cbat_vsa change silently ships a stale plugin),
      output under `/tmp/opencode/restriction-removal/baseline-coreutils`.
- [ ] A per-sub wall-time record (and stage breakdown where the pipeline
      provides one: lift / llc+link / run) saved to
      `/tmp/opencode/restriction-removal/baseline.md` — include the semantic
      PASS/FAIL summary line too (it doubles as a no-regression record for
      the fusion).
- [ ] The corpus gate numbers on this exact tree recorded in the same file
      (run_corpus 32/32 rc=0, check_allocas, run_semantic_all 29/3 + 8/8) —
      the baseline file is ticket 02's parity reference.
- [ ] NO source files modified; no commits.

Gate: the baseline file exists with real numbers; the tree is clean after.
