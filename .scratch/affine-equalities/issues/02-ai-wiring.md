# 02 — Wire the fused domain into the abstract state

**Status:** done (merged 35d9d54 2026-09-03; 523 ok / 0 FAIL; IR byte-identical control vs test)
**Depends on:** 01
**Blocks:** 03

**What to build:** the abstract state imports the fused domain for its word component; transfers, joins, meets, equality, and the split widening flow through it. Memories and frame untouched. Behavior must be identical to intervals on every existing gate (the domain carries the same bounds; equalities add facts nothing reads yet).

**Done when:** full unit suite green with zero behavior change vs the parent commit (IR-identity on the corpus is the tripwire — any diff here is a wiring bug, not a precision change).
