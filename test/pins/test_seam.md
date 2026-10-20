# Seam pins

Module `test/unit/test_seam.ml` (ids `SEAM-01`…`SEAM-05`).  Mechanism: the
Test_seam fixtures over the producer's real context — `mk_rctx` wires
the landmark table and the non-negativity oracle the fixpoint uses.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| SEAM-01 | the seam's `mk_rctx` builder wires production's non-negativity oracle, so the SLT row on a provably non-negative load is `[0,4]` | drop the non-negativity oracle from `mk_rctx` in `src/cbat_vsa/cbat_vsa.ml` | the row is the full signed hull → `Ws.precedes` fails |
| SEAM-03 | a refine under the context's widening head records the empty meet's boundary in the context's own table | drop the `with_widening_head` binding around the walk | `entries_for_head` is empty → fails |
| SEAM-04 | `x := y * -1` over a provably non-negative `y` is not a non-negativity proof: the SLT row keeps the reachable negative values | make `prove_nonneg`'s TIMES arm ignore the multiplier's sign | `-1` is excluded from `x`'s row → `Ws.elem` fails |
| SEAM-05 | `refine_edge_inline`: an empty guard meet is a dead edge; a satisfiable or merely narrowing guard and a discarded walk are not; an unreached read, a defined-flag guard, and a constant-false guard stay dead. | Make `refine_edge_inline` return the input env for an empty meet. | SEAM-05.empty-meet FAILs: the edge is not `AI.bottom`. |
