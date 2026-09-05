# 03 — The A/B + tag-stability gate + AGENTS.md

**Status:** blocked by 01, 02
**Depends on:** 01 (behavior), 02 (fixtures pinning it)
**Blocks:** (none — the closing ticket)

**READ FIRST:** the C8 spec §3 (the acceptance bar); the C1 ticket-03
precedent (`.scratch/c1-walk-budget/issues/03-ab-and-docs.md` — same gates,
same control discipline); the AGENTS.md validation-state section (the
battery commands); the A/B precedent in `73b4756`'s message (interleaved
rounds; the host runs ±15%).

**Tasks:**

- [ ] **Control:** fresh emissions + subtimes + stage anchors from the
      pre-change tree (a detached worktree at the merge-base — build +
      install there; the C1 ticket-03 control worktree pattern).
- [ ] **Tag-stability gate:** per-sub tag counts (0 moved of 2,421 is the
      bar C1 set) AND kind multisets on every heavy sub (e350/8cb0/6b60/
      296a0/9f00/9570 + gcc-12's top subs) vs control. ANY movement is a
      finding with direction + magnitude — the gate that carries the whole
      proof, since byte-identity is structurally off the table.
- [ ] **Battery:** corpus 35/35 rc=0; `check_allocas`
      identical-failure-class; `run_semantic_all` same 30/5; 8/8 oracle.
- [ ] **A/B timing:** 2+ interleaved rounds × {sort, grep, gcc-12} ×
      {control, change}; stage-counter attribution (visits DOWN — the
      scaffold count is the direct measure; walk/denote/join/equal counts
      DOWN proportionally to skipped visits; `denote` call counts must move
      with visits since every dequeue runs fully).
- [ ] **Docs:** AGENTS.md validation state rewritten (fresh numbers +
      the tag verdict + the IR-identity expectation set correctly:
      byte-identity NOT required, tag-stability IS); the C8 report card in
      `/tmp/opencode/architecture-review-20260905-0130.html` updated by the
      orchestrator, not this ticket.

**Verification:** everything green-or-explicitly-judged + the A/B table with
the tag-stability verdict; commit message carries the full numbers.
