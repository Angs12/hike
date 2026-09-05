# 03 — The A/B measurement + the tag-stability gate + the docs

**Status:** blocked by 01, 02
**Depends on:** 01 (enforcement), 02 (fixtures pinning the semantics)
**Blocks:** (none — the closing ticket)

**READ FIRST:** the spec (`.scratch/c1-walk-budget/spec.md` §3 — the
acceptance bar is grilling-settled); the AGENTS.md validation-state section
(the battery commands); the A/B precedent in `73b4756`'s commit message
(interleaved rounds, control vs change, the discipline for the host's ±15%).

**Tasks:**

- [ ] **Emit the control** from the pre-change tree (`e4b309c`, the
      `perf-arch-10-10` worktree has it — or a fresh detached worktree);
      emit the change build; run the **tag-stability gate**: per-sub tag
      counts (`zz_scratch_probe/subtimes.exe`, the `tags` column) AND kinds
      (`dump_tags.exe` or the memostats class on the vsa-debug build)
      over sort/grep/gcc-12 — diff against control. Record ANY movement in
      the A/B notes. If a kind moves (Range→Unbounded), raise C
      (1024→4096), re-verify, and record the raise; if counts move only,
      decide explicitly (the spec's decision point).
- [ ] **The battery:** corpus 35/35 rc=0; `check_allocas` (fixtures
      172/0; the 3 pre-existing shape-d fails on the real binaries must
      be IDENTICAL to control); `run_semantic_all` 30/5 with the SAME 5
      failing names; the 8-bin oracle 8/8.
- [ ] **The A/B timing:** 2+ interleaved rounds × {sort, grep, gcc-12} ×
      {control, change} using `subtimes.exe` totals + `stage_timer` on
      grep sub_e350 + sort sub_9f00 (the walk-lane attribution: `walk`
      seconds and pops DOWN, `denote` call counts FLAT — the budget touches
      only walk pops).
- [ ] **The docs:** AGENTS.md validation-state section rewritten (fresh
      numbers, fresh timestamp, the A/B table); the ADR — extend
      `docs/adr/0002-single-pass-trace-partitioning.md` with a Consequences
      addendum (the walk is now budget-bounded per SCC; a truncated walk
      was always sound, the budget picks where the cap lands) or write a
      short standalone ADR referencing it — pick by length; the report card
      C1 in `/tmp/opencode/architecture-review-20260905-0130.html` is
      updated by the orchestrator, not this ticket.

**Verification:** everything green + the A/B table with the recorded
tag-stability verdict; commit message carries the full numbers.
