# 17: Verify/close the 10 green-gate issues

**What to build:** The ten `.scratch/gate-green-context/issues/*` checklists (stack GEP helper, mixed-shape consume, vacopy variadic, deep-recursion threading, nested-calls threading, fizzbuzz widening, glossary syncs, dune unit gate) are verified green or their fixes landed, so "all gates pass". These existing issue files are the sub-work; this ticket integrates them.

**Blocked by:** T16 (dune build + runtest green).

**Status:** ready-for-agent

- [ ] Each of issues 01–10 in `.scratch/gate-green-context/issues/` is verified/closed (or its fix landed and checked)
- [ ] No red gate remains
