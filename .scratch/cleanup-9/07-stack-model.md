# Ticket 07 — stack model (regions/escape/plan)

Deps: none. One battery-verified commit. The R12 region fixtures and the
region-merge lane's sweep/determinism fixtures are the pins.

Merges:
- The region builder's two full-sub walks (the def-by-tid map and the
  def-width map are two identical folds over the same defs; the width walk
  discards everything the first keeps) → ONE walk producing an
  addr-and-width index per def; the member loop's re-extraction and the
  outgoing-store test's re-extraction read the index.
- The two Range arms in the stack-to-locals conversion-table fold (the
  singleton-tag arm and the general arm re-do the span-singleton test and
  the slot selection) → one arm with the singleton test inside.
- The memory-shape predicate's dead accumulator arm (`acc || true` is just
  `true`) — simplify; optionally share ONE has-mem-node predicate across
  the model, the emitter's node finder, and the extraction's address
  visitor (three implementations of "contains a memory node" today).

Hoists:
- The per-def fact index: the same defs are re-walked (address extraction,
  store-data extraction, free vars, memory shape) by SIX consumers on one
  sub — the region builder (three sites), both escape analyses, the
  unbounded test, the ABI-visibility test, and the conversion pass's cell
  fold; each extraction allocates a visitor object. One index built per
  pass entry feeds them all. This is the ticket's perf item: measure with
  the subtimes probe before/after; gate on byte-identity (the escape lane
  was articles 6+7's subject — the remaining waste is the repeated
  extraction, not the scans).
- ⚠ Do NOT fold the degraded-sub region recompute (the conversion pass's
  empty-info fallback) into the index — it is the degraded production path
  and measured at ~2 ms/binary; it stays.

The (sp, fp) parameter-pair → ABI-record threading across the model's
exp-walk family: ~8 functions thread the pair that is exactly the ABI
record's first two fields; the pass lane already computes the record once.
Signature churn touching test call sites (they pass the fixture ABI record
or the SysV default) — behavior-identical, but it is the one item here that
moves signatures, so it can drop to its own rider commit if the review
prefers.

Also measured-decision (no action without a fresh number): the worklist
pop's linear scan is the last O(n²) in the driver — IF this ticket's
subtimes A/B shows the pop lane ≥ 1% on grep/gcc-12, replace with a
position-indexed pop; otherwise record the non-finding and move on.

Acceptance: full battery; corpus IR byte-identity 32/32 (region ids are
post-region-merge numbering — compare against the re-baselined reference);
R12 fixtures green; subtimes A/B recorded in the commit message.
