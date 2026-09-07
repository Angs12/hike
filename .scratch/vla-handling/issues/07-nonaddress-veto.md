# VH-07 — Non-address Unbounds stop vetoing the plan

**Status:** done (merged f0615f8 2026-09-04; 615 ok / 0 FAIL; 7 subs flip convertible corpus-wide — emission+semantics must re-run at battery)

**What to build (fifth rule P3):** the 18 non-address flag/guard Unbounds (syntactically address-free — BinOp rhs, non-sp/fp values) must stop vetoing via `tags_inside_or_disjoint`: only syntactically address-carrying defs participate in the inside-or-disjoint check. The existing veto census (0 address-carrying of 19) is the fixture. Soundness case: a non-address def cannot denote a memory access, so excluding it from a memory-membership check loses nothing.

**Done when:** plan no longer vetoes on flag/guard Unbounds; genuine address-carrying Unbounds still veto; suite green.
