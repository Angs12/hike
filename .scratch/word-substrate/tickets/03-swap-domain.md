# T3 — Swap the domain onto Cbat_word

Blocked by: T1, T2
Blocks: T4

## Goal

Replace `Bap.Std.Word` as the domain's numeric substrate. No dual-track
production code: the referee stays in `clpequiv` (spec decision 3).

## Do

1. `src/cbat_vsa/cbat_clp.ml:18` — `module W = Word` → the new module.
   This is the single chokepoint for ~35 call sites in this file.
2. `src/cbat_vsa/cbat_word_ops.ml` — migrate its `W.*` calls.
3. `src/cbat_vsa/cbat_fin_set.ml` — its `Word`/`WSet` usage; `t = WSet.t
   * int` keeps its shape, only the element representation changes.
4. `src/cbat_vsa/cbat_clp_set_composite.ml` — `Clp of Clp.t | FinSet of
   FinSet.t`: unchanged in shape.
5. Keep `Word.t` only where BAP fills the value (the `WordSet.S`
   signature's `word` type at the BAP-facing edge, and `AI`'s interop).

## Rules

- **No semantic change.** Every op keeps its current result on the
  reference values — `clpequiv` is the oracle.
- **No dune change** in `cbat_vsa_domain` (see T1's note).
- The 129-bit intermediates (`dom_size ~width:(2*width + 1)`,
  `mul_exact`) go down the `Big` path by construction. Do not "optimize"
  them: they genuinely exceed 62 bits.

## Gate

- `dune build` green, both profiles.
- `clpequiv`: 0 mismatches across the whole dense sweep.
- `dune runtest`: 467 ok, 0 FAIL.
- Nothing else in this ticket — verification is T4.
