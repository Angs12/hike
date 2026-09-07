# 01 — Shared whole-map memo core

**Status:** ready-for-agent
**Depends on:** none (spec `.scratch/shared-memo/spec.md` decided)
**Blocks:** 03

**What to build:** the memo itself, behind a new internal seam inside the fixpoint
module. No interface change on the library seam; no pass, gate, or tag.

- [ ] Whole-map store keyed by (block, solution version): the value is the complete
      definition-to-produced-value map for that version. Single lookup per
      block-visit; per-definition reads as the retained sequential walk reaches them.
- [ ] Populate-on-miss from both paths (vertex transfer denotation and deep-walk
      produced-value computation); duplicate stores must agree by construction
      (determinism in definition + versioned solution state).
- [ ] Overwrite-on-bump eviction: one map per block retained; a version bump replaces.
- [ ] Walk path converted to read (meet + constraint derivation + live-set threading
      unchanged; walk extent and step cap unchanged). A miss behaves exactly as today
      plus one lookup.
- [ ] Version-bump audit: every mutation path affecting a block's solution state
      (including flag states and call facts) bumps that block's version; each
      audited path named in the report, any silent path fixed as a soundness bug.
- [ ] No hit-rate counters or profiling stages in production builds.

Gates:
- [ ] Unit suite 0 FAIL (incl. the strict jne-counter acceptance check).
- [ ] Corpus emission byte-identical to the pre-change tree (re-emit and diff —
      this ticket is precision-neutral by construction; any diff is a bug).
- [ ] Structural asserts 0 failed; semantic gates unchanged (same known failures only).
