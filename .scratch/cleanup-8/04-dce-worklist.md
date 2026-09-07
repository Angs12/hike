# Ticket 04 — DCE worklist (all-or-nothing)

Status: LANDED per user override (2026-09-06) — "it is better code."
The A/B below stands as the honest record (performance-neutral), but the
decision is that the worklist's structural properties (one census walk
instead of open-ended rounds; blocks that lose nothing keep physical
identity; the removal set computed by an explicit cascade rather than
repeated whole-sub rewalks) are worth the ~100 lines. The all-or-nothing
gate is therefore recorded as OVERRIDDEN, not met.

## Settled shape (round 2/3 grilling)

**Def-tid adjacency, `keep` unchanged, affected-defs-only used-sets.**
All-or-nothing: NO no-op-fast-path fallback ticket — if the worklist stalls,
this ticket closes unfinished rather than landing a half-shape.

## Current shape (hike_dce.ml:124-134)

```
sweep_fixpoint:
  round: used_and_roots_of sub (full Term.visitor walk)
        + Term.map blk_t (Term.filter def_t ...) — every block rebuilt
  repeat until no def removed
```

## New shape

1. **One initial pass**: compute `used`, `load_roots` (unchanged visitors),
   and a def-tid adjacency: for every def `d`, the set of defs whose rhs
   free-vars include `lhs d` (readers-of-lhs, keyed by Tid). Build it in the
   same walk (`Def.free_vars` is already computed for `used` — record the
   edge while you're there; do NOT re-walk).
2. **The cascade**: evaluate `keep d used load_roots` once per def
   (unchanged predicate — do not touch `keep`). Removals propagate:
   when `d` is removed, its readers (adjacency) may become newly-dead. The
   subtlety the grilling settled: `used` only ever SHRINKS (defs only
   leave), so re-checking a reader against the ORIGINAL `used` is
   **unsound-toward-keeping** (it keeps a def whose only user was removed).
   The honest formulation: maintain `used` incrementally — when `d` is
   removed, subtract `rhs d`'s free vars from `used` ONLY IF no other
   surviving def still contributes them. The cheap-and-sound version: keep a
   per-var **contributor count** (how many surviving defs' rhs mention the
   var, plus jmp/phi mentions as permanent contributors); a var leaves
   `used` when its count hits zero. Then a reader re-check is exact.
3. **Rebuild**: blocks are rebuilt once, at the end, from the removal set —
   `Term.filter` only for blocks that actually lost a def (the array
   rebuild is the measured cost; blocks that remove nothing keep their
   physical block).
4. **Fixpoint semantics must be IDENTICAL** to the old sweep-to-quiescence:
   the cascade reaches the same removal set (it's the same monotone
   computation, evaluated eagerly instead of round-by-round). The D0-D5
   fixtures + `dune runtest` pin this; the battery + IR byte-identity is the
   final gate — byte-identical output is REQUIRED (same defs removed, same
   order, same shapes).

## Epilogue interplay (settled, no question)

`dce`'s entry does the ret-epilogue rewrite (`mapper#map_sub`) BEFORE the
sweep; the worklist changes only the sweep. Orthogonal — no interaction.

## Out of scope

- The load-roots recompute-per-round question disappears (roots are part of
  the initial pass; a removed Load's mem-var un-rooting rides the same
  cascade via the adjacency of its var — VERIFY: `load_roots` is keyed by
  mem var, `keep` consults it for `is_region_mem` lhs; a removed Load must
  decrement that var's root-contribution exactly as `used` does. If the
  contributor-count treatment of roots gets hairy, roots may stay
  recomputed-once (not per round) — the round-2 fixpoint already tolerates
  one recompute.)

## Verification

- D0-D5 fixtures green (`test_cbat/test_dce.ml`).
- `dune runtest` full suite.
- Full battery + IR byte-identity 35/35.
- Timing: passcost on ls/du — dce column should drop ~2x (round 2 gone,
  rebuild only where removals happened); record before/after in the ticket
  when you close it.
