# Ticket 02 — VSA: `prove_nonneg`'s anchor becomes frame-term-based

Blocking: 01. Blocks: 03.

## Change

The one fp-by-name site inside the VSA that feeds semantics: `prove_nonneg`'s
`stack_anchor` (`cbat_walk.ml:171` via `is_stack_reg`, consumed at `:240` —
"anchored = every free var of the address is a stack register"). It feeds the
SLT/SLE `known_nonneg` refinement (`cbat_walk.ml:95-104`).

Replace the name test with the value-true form: **"every free var of the address has
a frame term in the current state"** — `frame_lookup`/`frame_of` over the abstract
env's frame map. This preserves the -O0 refinement EXACTLY (RBP carries a frame term
there via its prologue def — the non-negativity proof is unchanged) and drops
heap-RBP correctly (no frame term → not anchored — a heap-valued address gains no
unwarranted non-negativity proof).

Mechanics: `stack_anchor` takes the env (it already has it at `:240`'s call site) or
becomes a closure over the current frame; the `is_stack_reg` reference dies. Where
the anchor result feeds `known_nonneg`, the value must be a CONSTANT offset (fconst)
for the induction to hold — verify the existing arithmetic uses the term's constant
part and keep that discipline; a term carrying fvars does not prove a constant bound
(an fvars-carrying address is not anchored — its value varies with the index).

## Notes

- Not unsound today (non-negativity is proven from stored values), but it is the
  by-name assumption inside the VSA; this ticket is the VSA's whole share of the
  lane's code changes (the tagging path, `constrain_cell`, `frame_add_rsp`, call
  frame-keeping, VLA detection are all already sp-only/value-based — UNCHANGED).
- `preserved_of_sub` does NOT change here (behavior identical; the field-level
  rewrite happens at T6).

## Gates

- `dune runtest` — no existing check may move (R12-series, P-series, T-series all
  green; the backward-lane cell_at fixtures unaffected — they exercise cell keys,
  not the anchor).
- -O0 corpus IR byte-identity 32/32 vs the control (RBP carries a term at -O0 →
  the anchor holds wherever it held before — expected identity; any delta means
  the frame-term lookup disagrees with the name test on a real binary —
  investigate before landing).
- Full battery + probes (vsa_debug fixture traces where nonneg fires).
