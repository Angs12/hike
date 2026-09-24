# Pins — test_backward

Module `test/unit/test_backward.ml` (group `backward`, ids `BK-01`…`BK-78`).
Merges `test_cbat/test_backward.ml` (the backward-refinement pins) and
`test_cbat/test_seed.ml` (the inverse-denotation pins) into one process;
the backward pins come first (`BK-01`…`BK-56`), the seed pins after
(`BK-57`…`BK-78`).  Every source `check` site is carried as one pin; none
retired (`L3c2-6` carried no assertion and is not a site).

There is **no `Test_seam` fail-before switch** for this lane, so — per the
lane spec `§Fail-before` — the disable recipes below are textual inversions
of the pinned mechanism, and the red is re-demonstrated by review whenever
the cited mechanism changes.  Production `src/` is never modified.  Each pin
builds its own fixture inside its closure (no cross-pin state).

Mechanisms live in `src/cbat_vsa/cbat_backward.ml` (the inverse denote, the
deep walk, `constrain_edge`), `src/cbat_vsa/cbat_vsa.ml` (the fixpoint's
inline edge refinement), `src/cbat_vsa/cbat_ai_memmap.ml` (the cell merge),
`src/cbat_vsa/cbat_call_effects.ml` (the matched-pair SP restore), and
`src/hike_jump.ml` (the jcc/flag decoder).

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| BK-01 | L3a PLUS row: the walk's per-def producer subtraction through `operand_constraints`' PLUS arm met `{4}` into the `[RBP-8]` load cell. | In `cbat_backward.ml`'s `inverse_denote`, make the general `Bil.BinOp` `_` arm `env` (skip `operand_constraints`). | BK-01 (`bounded_above` false; cell stays top). |
| BK-02 | L3a MINUS row: the subtraction pre-image `[1,10]`. | As BK-01 (the same general BinOp arm). | BK-02. |
| BK-03 | L3a LSHIFT-const row: the shift pre-image `[0,9]` (40>>2). | Drop the shift arm's row (`| Bil.BinOp ((LSHIFT\|RSHIFT\|ARSHIFT), _, _) -> env`). | BK-03. |
| BK-04 | L3a TIMES over an unbounded operand is the identity (sound stop). | Invert the stop: make the TIMES arm return a bounded hull instead of identity. | BK-04 (`not (bounded_above … 19)` becomes false). |
| BK-05 | L3a NEQ guard is doubt: `cmp_inverse` leaves the env for NEQ. | Make the NEQ case walk the complement (`neq_complement`) instead of `env`. | BK-05 (`Ws.is_top` false). |
| BK-06 | L3c1-1 flag record: `Hike.Jump.compile_sub`'s `cross_guard`/`plan_block` recovers `CF := SLT(t,10)` from a bare `when CF`. | In `hike_jump.ml`, make `plan_block` return `[]` (no flag rewrite) so the guard stays `Bil.Var cf`. | BK-06 (cell stays top). |
| BK-07 | L3c1-2 a redefinition of the compared operand makes the guard constant-false; the taken edge is dead (`Ws.is_bottom`). | Make `read_def` position-insensitive (return the load def even when a later def redefines the operand). | BK-07 (cell is refined, not bottom). |
| BK-08 | L3c1-3 a non-comparison flag redefinition invalidates the record (`extract_facts` returns `None`). | Treat `Bil.Unknown` as a fact-producing rhs in `extract_facts`. | BK-08 (cell refines). |
| BK-09 | L3c1-4 multi-def base: the per-block producer subtraction yields the EXACT body-IN window `[1,10]`. | Run the walk raw: `walk_block ~raw:true` (skip the producer subtraction). | BK-09 (wider join; 11 ∈). |
| BK-10 | L3c1-5 direct `constrain_edge` has no defs, so the flag-state arm is gated off (cell top). | Make `constrain_edge` recover a bare flag var's reaching comparison. | BK-10 (`Ws.is_top` false). |
| BK-11 | L3c2-1 `constraint_row` SLT gates on `provably_nonneg` (the seeded counter). | Force `provably_nonneg = false` in `constraint_row`. | BK-11 (two-piece row; `bounded_above … 3` false). |
| BK-12 | L3c2-2 the two-piece SLT total row for an unproven operand. | Drop the `total_row` fallback in `guard_row` for SLT (return `None`). | BK-12 (cell top). |
| BK-13 | L3c2-3 `c >= half` SLT/SLE single high interval. | Drop the `if c >= half` branch in `constraint_row`. | BK-13 (`l3c2_in_high` false). |
| BK-14 | L3c2-4 flag-indirected signed guard (record + signed row). | As BK-06 (`plan_block = []`). | BK-14. |
| BK-15 | L3c2-5 trace-exact cell refinement with no RBP prologue def (`constrain_cell_on_trace`). | Make `constrain_cell_on_trace` the identity (`fun ~env … -> env`). | BK-15. |
| BK-16 | L3c3-1 PLUS-HULL: the circular hull `{−1} ∪ [0,8]` on `t`. | As BK-01 (PLUS arm identity). | BK-16. |
| BK-17 | L3c3-2 TIMES over an unbounded operand is the identity (sound stop). | As BK-04 (force a bounded TIMES answer). | BK-17. |
| BK-18 | L3c3-2b seeded operand: the guard's signed row bounds `t`, so the exact TIMES slice applies. | Drop the TIMES slice in `operand_constraints` (return `None,None` for TIMES). | BK-18. |
| BK-19 | L3c3-3 RSHIFT-const row. | As BK-03 (drop the shift arms). | BK-19. |
| BK-20 | L3c3-4a ARSHIFT-const row with a provably non-negative operand. | Make the ARSHIFT arm consult `nonneg` and return identity when it holds. | BK-20. |
| BK-21 | L3c3-4b ARSHIFT on a top operand is a sound stop (identity). | Remove the non-negativity gate so ARSHIFT always refines. | BK-21 (`Ws.is_top` false). |
| BK-22 | L3c3-5 TIMES k = 0 is the identity. | Invert the k=0 stop (return a row). | BK-22 (`Ws.is_top` false). |
| BK-23 | L3c3-6 TIMES EQ non-divisible is the empty pre-image (no refinement). | Invert the divisibility check so the row is non-empty. | BK-23 (`bounded_above … 39` becomes true). |
| BK-24 | L3c4-1 Var-vs-Var LT: `overlap_constraints` caps `t` at `u`'s max. | Make `overlap_constraints` the identity (`fun _ _ _ -> None,None`). | BK-24. |
| BK-25 | L3c4-2 a TOP Var-vs-Var operand makes the refinement vacuous. | Force `overlap_constraints` to emit `[0,c]` even when an operand is top. | BK-25 (`not (bounded_above … 1000)` false). |
| BK-26 | L3c4-3 DIVIDE-const row. | Drop the DIVIDE arm in `inverse_denote` (identity). | BK-26. |
| BK-27 | L3c4-4 HIGH-extract producer row (`high_cast_constraint`). | Make `high_cast_constraint` return `None`. | BK-27. |
| BK-28 | L3c4-5 DIVIDE k = 0 is a sound stop (identity). | Remove the k=0 guard so DIVIDE 0 refines. | BK-28 (`not (bounded_above … 39)` false). |
| BK-29 | L3c5-1 const-first EQ normalizes to const-second (`cmp_inverse`'s `Bil.Int c0, e0` arm). | Drop the const-first arm in `cmp_inverse` (`| Bil.Int _, _ -> env`). | BK-29. |
| BK-30 | L3c5-2 MOD has no closed form — identity. | Remove the MOD identity arm and add a row. | BK-30 (`not (bounded_above … 39)` false). |
| BK-31 | L3c5-3a AND-identity row (`t AND ~0 ≡ t`). | Drop the AND/OR identity rows in `inverse_denote`. | BK-31. |
| BK-32 | L3c5-3b OR-identity row (`t OR 0 ≡ t`). | As BK-31. | BK-32. |
| BK-33 | L3c5-4 an Unknown condition keeps the env unchanged (never asserts). | Make `inverse_denote`'s `Bil.Unknown` arm return `AI.bottom`. | BK-33 (`AI.equal` false). |
| BK-34 | L-3b equal-lower merge: the mem map coalesces the `[RSP-8]` point-key pile to ≤ 3 cells. | In `cbat_ai_memmap.ml`, make `Mem.add` always a fresh node (no coalesce). | BK-34 (`l3b_cells_of > 3`). |
| BK-35 | L-3b partition: the iterate view vs the exit view hold different cells. | Drop the trace-taken view (union the body IN state with the exit state). | BK-35 (exit cell loses `{8}` / iterate cell top). |
| BK-36 | L-3b +1-adjacent equal-value merge arm. | Remove the +1-adjacent arm in the coalesce (keep only equal-lower). | BK-36 (`l3b_cells_of = 1` false). |
| BK-37 | B-1 an interrupt edge is an unknown external callee: RSP anchor kept, `rdi` topped. | Make the `Int` edge drop the caller frame (whole-memory top). | BK-37 (RSP anchor lost). |
| BK-38 | L-B1 jcc decoder: the `jle` compound guard recovers SLE(c=3). | In `hike_jump.ml`, drop the `join`/`eval_bexp` OR-of-ZF-and-sign recovery. | BK-38 (cell top). |
| BK-39 | L-B2 the `jl` compound guard emits SLT. | Drop the `signed_item`/xor-core recovery. | BK-39. |
| BK-40 | L-B3 the `ja` guard emits UGT (`~(CF|ZF)`). | Drop the CF complement (`rel_complement`) handling. | BK-40. |
| BK-41 | L-B4 the same-comparison gate rejects a mixed second-cmp group (cell top). | Relax the same-comparison gate in `plan_block` to accept the mixed group. | BK-41 (`Ws.is_top` false). |
| BK-42 | L-B5 the record path (bare `when CF`, unique load def) survives. | As BK-06 (`plan_block = []`). | BK-42. |
| BK-43 | L-D2 the wide-bound counter's non-negativity survives widening (max ≤ 63). | Drop the landmark-directed widening's non-negativity carry (`Cbat_landmarks`). | BK-43 (`bounded_above … 63` false). |
| BK-44 | E1-1 the ON-path matched-pair `+word` RSP restore keeps the loop header at `{0x1000}`. | In `cbat_call_effects.ml`, delete the matched-pair restore arm. | BK-44 (RSP drifts by 8 per call). |
| BK-45 | E1-2 straight-line call: the continuation RSP is exactly `{0x2000}`. | As BK-44. | BK-45 (RSP `{0x1ff8}`). |
| BK-46 | L-D6 RBP-anchored gate-free loop: the jcc meet binds `[RBP−8]` at BODY input. | As BK-06 (no flag rewrite) or skip the dead epilogue denotation. | BK-46 (cell top). |
| BK-47 | R2-1 inline-arithmetic condition `(t+1) < 64`: the producer recursion yields the 64-element hull. | Drop the inline-BinOp fallthrough in `constrain_def_chain`/`cmp_inverse`. | BK-47 (cardn > 64 / top). |
| BK-48 | R2-2 NOT-of-comparison: the NOT-edge keeps its env (the false-edge row never confines the taken edge). | Make the `has0` arm apply the false-edge row to the taken edge. | BK-48 (`bounded_above … 4` becomes true). |
| BK-49 | R2-3 const-first LT flip dispatches UGT (`10 < t` → `[11, 2^w)`). | Drop `flip_guard_op` for the const-first arm. | BK-49. |
| BK-50 | R2-4 nested TIMES chain: the exact no-wrap slice yields the body-IN singleton `{63}`. | Drop the TIMES no-wrap slice. | BK-50 (`Ws.equal` false). |
| BK-51 | M5-1 the MINUS wrap hull `{0xFFFFFFFF, 0..3}` (cardn 5). | Make the wrap hull return the unwrapped interval only. | BK-51 (cardn ≠ 5). |
| BK-52 | M5-2 TIMES k=0 identity. | As BK-22. | BK-52 (`Ws.is_top` false). |
| BK-53 | M5-3 XOR-~0 bijection `{~5}`. | Drop the XOR/lnot bijection row. | BK-53. |
| BK-54 | M5-4 LOW cast in the walk: truncation hull `[5, 0xFFFFFF05]`. | Make `low_cast_constraint` return `None`. | BK-54. |
| BK-55 | M5-5 signed-division rule `{−6,−5}`. | Drop the SDIVIDE arm. | BK-55. |
| BK-56 | M5-6 Var-identity row propagates through the copy (`≤ [0,9]`, not `[0,10]`). | Drop the `Bil.Var` identity propagation in the walk. | BK-56 (`bounded_above … 9` false). |
| BK-57 | T1 the RSP-based same-block cell meet (`constrain_cell_on_trace` meets `[RSP-8]` into the offset key). | Make `constrain_cell_on_trace` the identity. | BK-57 (cell unchanged; `15 ∈`). |
| BK-58 | T2 the dynamic-index meet: the index's iterate range confines the key hull. | Skip the index constraint in `constrain_cell_on_trace` (meet all keys). | BK-58 (cell at 40 refined too). |
| BK-59 | T3 the ranged meet's overlap boundary (the `[0,64]` cell splits at `[8,24]`). | Make `Mem.meet_range` meet the whole cell (no split). | BK-59 (offset 0 narrowed). |
| BK-60 | T4 the exit-side cells survive the iterate-range meet. | As BK-58 (meet everything). | BK-60 (offset 40/80 narrowed). |
| BK-61 | S1 EQ const-second seeds the Var `{10}` (`row_for EQ`). | Make `row_for`/`constraint_row` EQ return `None`. | BK-61 (`10 ∈` false). |
| BK-62 | S2 NEQ const-second is the wrapped complement (`neq_complement`). | Make the NEQ row the identity. | BK-62 (`11 ∉`). |
| BK-63 | S3 SLT const-second is the two-piece `[0,3] ∪ [2^31,max]`. | As BK-12 (drop `total_row` for SLT). | BK-63. |
| BK-64 | S4 const-first LT flips to UGT (`[11,max]`). | As BK-29 (drop the const-first arm). | BK-64. |
| BK-65 | S5 Var-vs-Var LT overlap caps `t` at `u`'s max. | As BK-24. | BK-65. |
| BK-66 | S6 Var-vs-Var NEQ is the complement of the `{5}` overlap. | Make the NEQ overlap identity. | BK-66. |
| BK-67 | S7 generic comparison with producer recursion (`(u+1)`'s value set seeds `u`). | Drop the producer recursion in `cmp_inverse`. | BK-67. |
| BK-68 | S8 producer PLUS hull `{0xFFFFFFFF} ∪ [0,8]`. | As BK-01. | BK-68. |
| BK-69 | S9 a load operand met its cell fact into the env's memory. | Make the `Bil.Load` arm identity. | BK-69 (cell unchanged). |
| BK-70 | S10 `complete_cond` of `NOT (t <u 10)` seeds the UGE side `[10,max]`. | Make `Cbat_vsa_utils.complete_cond` the identity. | BK-70. |
| BK-71 | S11 the NEG row (`neg` of the produced window). | Drop the `Bil.NEG` arm. | BK-71. |
| BK-72 | S13 the completed dual `NOT (t EQ 10)` → NEQ complement. | As BK-70. | BK-72. |
| BK-73 | S15a the LOW-cast truncation hull `[5, 5+2^32−2^8]`. | As BK-54. | BK-73. |
| BK-74 | S15b the SIGNED-ext pre-image `[0,0xFF]`; the empty meet keeps the env value (identity). | Make the empty meet narrow/pick the constraint. | BK-74 (`Ws.equal` false). |
| BK-75 | S16a `complete_cond` negates each of the six comparisons structurally (both orders). | As BK-70. | BK-75. |
| BK-76 | S16b the completed fallthrough of `(x <u y)` seeds `y ⊆ [0,3]`. | As BK-70. | BK-76. |
| BK-77 | S16c the 3-comparison AND chain narrows `a` to `[0,6]` and leaves `y`,`c`. | Make the `Bil.BinOp (AND, …)` `{1}` arm identity. | BK-77. |
| BK-78 | S14 an infeasible constant is `AI.bottom`; a consistent one is the identity. | Make `inverse_denote`'s `Bil.Int` arm always `env`. | BK-78 (bottom check false). |
