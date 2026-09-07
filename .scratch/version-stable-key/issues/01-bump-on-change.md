# 01 — Bump-only-on-change version discipline

**Status:** ready-for-agent
**Depends on:** none (spec `.scratch/version-stable-key/spec.md` decided)
**Blocks:** 03

**What to build:** semantic versions inside the fixpoint module. No interface change
on the library seam; no walk, seed, cap, or precision change.

- [ ] Store sites compare old versus new solution state and skip the version bump
      (and the store where sound) when equal; physical-equality fast path first.
- [ ] Lookup path untouched (integer compares over the stamped read set).
- [ ] Every store/bump site enumerated in the report; any path that can change
      reader-visible state without bumping is a soundness bug — fix as such.
- [ ] Miss behavior byte-for-byte today's walk (structure, step cap, threading).
- [ ] No production counters, stages, passes, gates, or tags.

Gates:
- [ ] Unit suite 0 FAIL (strict jne-counter check + F1-FT green).
- [ ] Corpus emission byte-identical to the pre-change tree (re-emit and diff —
      precision-neutral by construction; any diff is a stop-and-report bug).
- [ ] Structural asserts 0 failed; semantic gates at the known-failure floor.
