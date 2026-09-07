# Ticket 06 — emitter dedup (the 73-check emission wing is the local oracle)

Deps: ticket 03 (constants/params gone first). One battery-verified commit.

Merges inside the emitter (all behind the frozen 12-val seam — no public
surface moves):
- The FP-lane internal clones: the integer-width-or-default closure ×3, the
  bitcast-to-FP closure ×3, the trunc/zext coercion ×3, the ret list
  fetched twice per native call. Three named helpers replace ~8 inline
  blocks. ⚠ The 26-row native-FP table is pinned by the emission wing's
  per-row checks — do NOT touch the table or its rows; dedup only the call
  arms around it.
- The function-declaration lane: the ret-type trio duplicated verbatim, the
  args fold re-implementing the arg builder, the registration appearing
  twice → extract the ret-type-of-rets constructor + one register step.
- The const-address twins: the plain load/store const arms vs the
  RIP-relative const arms run the same dance; and every constant-address
  access scans the section list twice (guard + resolve). One const-load/
  const-store pair; the found section passes through.
- The three call-finishing tails (direct call, native FP call, external
  intrinsic call) + the duplicated extractvalue ret-binding loop → one
  call finisher + one ret binder. The SP-restore stays per-call-site (the
  pinned `%sp_restored` checks are the oracle that it stays).
- The frame-geometry triple: the degraded-dims builder and the sub-emitter
  frame arm implement the same recipe with two differently-written align-16
  rounds, and the geometry walker carries a no-op arm + an obfuscated
  negation. ONE producer (home: the stack model), the seam's exported
  dims function stays the contract. The honest-gate deleted the stale
  C2/A2/A3 expectations, so the seam callers are the only pins — write the
  equivalence as unit checks (equal outputs on a fixture) BEFORE deleting
  the second implementation.
- The mem-marker Load/Store twins: one marker factory + shared skeleton.
  The marker names and their insertion order feed the per-block local map
  keys — keep sequencing byte-identical.

Hoists riding this ticket:
- The per-callsite whole-sub rescans: the cast-source-width fold (runs once
  per int→float call site — hoist to per-sub), the libm membership lists
  (string-set at init), the per-arg block scan. IR byte-identical by
  construction.
- The context-get pairs: one emitter-env reader halves the boilerplate of
  the ~20 function openings.

Acceptance: full battery; corpus IR byte-identity 32/32; the emission wing
green (it pins the FP table, the poison regime, the SP restore, the fission
golden by name).
