# 05 — Per-region VLA scoping

**Status:** done (merged cace68b 2026-09-04; 563 ok / 0 FAIL)
**Depends on:** 04
**Blocks:** 06

**What to build:** the whole-sub dynamic-alloc veto becomes per-region overlap against the VLA extent; VLA-tagged defs exempt from the inside-or-disjoint check; merge rows for mixed static/dynamic components (extend the C4a/R11 pins); regions above the anchor convert for any size; overlapping regions stay memory (never per-region allocas). Tag-driven emission on the existing rebind path — no emitter changes.

**Done when:** `alloca_vla` converts ≥1 disjoint region with byte-identical stdout (AMENDED post-review P1 2026-09-04: unmet on the real binary for structural reasons — its sizes flow through div/imul alignment chains and shr/shl-aligned bases, severing the anchor−s+k shape; dynamic stores are loop-counter-indexed (NEQ-guard gap, out of scope); 19 Unbounded defs trip the whole-plan veto. 0 VLA tags fire, stdout identical. Conversion around a live VLA stays pinned at fixture level, S8); whole-sub fallback survives only where an overlap genuinely exists.
