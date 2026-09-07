# 03 — Revive the VLA kind with anchor payload (dark)

**Status:** done (merged 37970dc 2026-09-03; 523 ok / 0 FAIL; dark by construction)
**Depends on:** 02
**Blocks:** 04

**What to build:** `VLA` of `{anchor, max_size}` through the three-site type edit (definition, signature mirror, vocabulary alias); wire the dead optional tid parameter at the single `classify` call site; per-def anchors computed at extraction by prefix-denoting RSP; explicit conservative arms at the four wildcard matches (model visibility, stl cells, audit probe, create_def fallback); `span_of`/merge/disjointness treat the extent as a pure interval. Unreachable in behavior (no membership rule yet): battery trivially green.

**Done when:** builds clean (exhaustiveness warning is error — every row explicit), suite green, IR byte-identical to the 02 commit.
