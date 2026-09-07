# Ticket 02 — the word-ops twin fold (referee-gated)

Deps: ticket 01 (the two dead exports gone first, shrinking this diff).
One battery-verified commit. The differential referee stanza in runtest is
the primary oracle.

Delete the `Cbat_word_ops` module: the word substrate now carries its whole
op set (the substrate's own interface section says so). Migrate:

- `cbat_clp`'s `open !Cbat_word_ops` — every unqualified use (cap_at_width,
  dom_size, factor_2s, bounded_gcd, mul_exact, add_bit, count_initial_1s,
  lead_1_bit, cdiv, half) either exists on the substrate already or moves
  with this ticket (add_bit / count_initial_1s / lead_1_bit live only in the
  twin — move them to the substrate's op set; lead_1_bit_run died with the
  honest-gate's fixed_bits, verify).
- The engine's `Word_ops.` sites (is_one → the substrate's is_one; half ×5).
- The composite's `gt_int` ×2 → the substrate (move `gt_int` over; it wraps
  a compare at the operand's width).
- The memmap's `endian_string` ×2 → move to the substrate (it is a display
  helper, not arithmetic; if that feels wrong, its natural second home is
  the shared utils module — pick ONE, record in the commit message).
- `test_common`'s and clpequiv's `Wo` aliases: the probe keeps a frozen
  verbatim copy of the old implementations as its REFERENCE oracle — do
  NOT edit the probe's reference bodies; only its module plumbing (the
  alias may point at the substrate with the reference copy staying local
  and frozen).

NOT in this ticket: any semantic change to an op. If two implementations
disagree (twin vs substrate), STOP — the disagreement is a substrate bug,
report it, don't merge.

Acceptance: `dune build` both profiles; full battery; the referee stanza
green (2.86M checks, 0 mismatches); corpus byte-identity 32/32 (the ops are
value-identical by construction — any byte diff is a red flag).
