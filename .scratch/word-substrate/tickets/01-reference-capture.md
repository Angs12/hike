# T1 — Capture the Z-based reference in clpequiv

Blocks: T2, T3 (the referee must exist and be green BEFORE anything changes)
Blocked by: nothing

## Goal

`clpequiv.ml` already inlines old (reference) implementations by design.
Before the substrate swap, the *current* `Cbat_word_ops` word
implementations move into it as the reference, and `clpequiv`'s sweep
cross-checks them against the unmodified production ops.

This validates the harness **while both sides are still identical** — a
green sweep here proves a later red sweep means a real divergence, not a
broken harness.

## Do

1. Read `zz_scratch_probe/clpequiv.ml` (existing reference inlining) and
   `src/cbat_vsa/cbat_word_ops.ml` (`mul_exact`, `add_exact`,
   `succ_exact`, `lshift_exact`, `bounded_gcd`, `cdiv`, `is_one`,
   `bounded_diophantine`, `factor_2s`, `dom_size`, `cap_at_width`).
2. Add a `Ref_word` section to `clpequiv.ml` holding the current
   implementations verbatim.
3. Extend the sweep: for every `(width, base, step, cardn)` it already
   walks, cross-check each word op reference-vs-production.
4. Report `checked=/mismatches=`.

## Gate

- `dune runtest` — 467 ok (or the current count), 0 FAIL.
- `dune exec zz_scratch_probe/clpequiv.exe` — mismatches **0** (both sides
  identical; any mismatch is a harness bug, not a domain bug).
- No `src/` change in this ticket.

## Note

Do NOT touch `src/cbat_vsa/dune`: `cbat_vsa_domain` has no cppo step, so
`#ifdef VSA_DEBUG` breaks the build there (documented breakage). Keep all
instrumentation in `zz_scratch_probe/`.
