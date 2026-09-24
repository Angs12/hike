# Seam pins

Module `test/unit/test_seam.ml` (ids `SEAM-01`…).  Mechanism: the
Test_seam fixtures over the producer's real context — `mk_rctx` wires
the landmark table and the non-negativity oracle the fixpoint uses.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| SEAM-01 | the seam's `mk_rctx` builder wires production's non-negativity oracle, so the SLT row on a provably non-negative load is `[0,4]` | drop the non-negativity oracle from `mk_rctx` in `src/cbat_vsa/cbat_vsa.ml` | the row is the full signed hull → `Ws.precedes` fails |
| SEAM-02 | the context's landmark table is empty before the widening window opens | seed the table in `mk_rctx` | `entries_for_head` is non-empty → fails |
| SEAM-03 | a refine under the context's widening head records the empty meet's boundary in the context's own table | drop the `with_widening_head` binding around the walk | `entries_for_head` is empty → fails |
