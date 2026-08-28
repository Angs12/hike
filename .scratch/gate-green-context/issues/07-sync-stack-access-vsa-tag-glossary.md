# 07: Sync Stack Access + VSA Tag glossary

**What to build:** The Language glossary entries for Stack Access and VSA Tag in CONTEXT.md match the implemented tagging scheme, so a reader can locate the single truth for stack detection and tag presence.

**Blocked by:** 01: Fix hike_stack GEP helper (rebase_addr)

**Status:** ready-for-agent

- [ ] `Stack Access` defined as `direct_sp` plus `addr_is_stack` conjunct (Load/Store/Cast shape containing RSP/RBP), with `relevant` separate and `direct_sp` not deleted
- [ ] `VSA Tag` defined as `vsa_kind = Range | Infinite(lo,hi) reversed-rep | VLA(tid)` plus `k_ranges`/`degraded`; invariant states `Range` qualifies, `Infinite`/`VLA` excluded from normal regions, `TOP` = absence → guarded poison / S2 cap
- [ ] `Avoid` lists no longer ban `direct_sp` or `untagged stack access` when referring to the real tag/diagnostic
