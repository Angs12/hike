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

Hoists (landed, scoped by measurement — see below):
- The per-def fact index (`def_facts_of_sub`: addr, store-data exp,
  mem-shape, free vars — one walk), feeding `sp_escaped` (kills the
  per-round re-walks in the grow loop) and `regions_of_sub` (one walk
  replaces the def-map + width walks AND the member/outgoing re-walks).
  NOT fed to `frame_addr_alias` / `has_unbounded_access`: both are
  single-pass with early exits (empty frame-vars, first unbounded def),
  and a prebuilt index forfeits the exit — measured +1.4% on grep when
  tried, reverted same session. The index is the no-early-exit shape
  only.
- The store-data extractor WITHOUT the wrapper closure (the model
  never rewrites); the closure-allocating spelling stays in stl's
  private use.

The (sp, fp) → Abi.t threading: RESCOPED TO NOTHING, deliberately.
`fp_of` returns None on unknown targets while the ABI record always
carries an fp; the R12 fixtures run on unknown targets with RBP frame
vars, so threading the record changes test behavior on unpinned
shapes. The residue was already abi-native (cleanup-8's ctx.abi,
ticket 03, ticket 06's geometry). Recorded so nobody re-proposes.

Measured-decision (pop_min): DONE, non-finding by measurement.
Temporary #ifdef counter (added, measured, reverted — never
committed): grep sub_e350 (996 pops, the heaviest sub) scans
7835 inner iterations at maxpend 14 (~8 compares/pop, two map finds
each) — sub-millisecond against the 1.1s fixpoint (<0.1%). The
scan stays.
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
