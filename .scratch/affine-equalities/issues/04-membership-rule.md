# 04 — Shared-variable membership rule (light-up)

**Status:** done (merged 25c67d8 2026-09-03; 552 ok / 0 FAIL)
**Depends on:** 03
**Blocks:** 05

**What to build:** the classify-time rule recognizing `anchor-s+k` address shapes as inside-VLA: same-var proof by full value numbering (decrement size var = address var, through single spills at minimum), const-k and symbolic-k-denominated offsets from the start, reduction-at-query for the bound inference. Emits the revived kind into the existing flow. No emitter changes.

**Done when:** the rule fires on `alloca_vla`'s dynamic addresses (or documents precisely why a given def still misses, with the missing proof named); suite green; diagnostics change only where addresses genuinely resolve.
