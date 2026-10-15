# Pins — test_backward

Module `test/unit/test_backward.ml` (group `backward`, ids `BK-01`…`BK-111`).
Merges `test_cbat/test_backward.ml` (the backward-refinement pins) and
`test_cbat/test_seed.ml` (the inverse-denotation pins) into one process;
the backward pins come first, the seed pins after.  Every source `check` site is carried as one pin; none
retired (`L3c2-6` carried no assertion and is not a site).

The pins consume `Vsa.Test_seam` (the constraint rows, the walk, and the
counting refine `refine_edge_count_writes`, whose `on_write` hook names
each actual env write).  Each pin builds its own fixture inside its
closure (no cross-pin state); the disable recipes below are temporary
inversions flipped in `src/cbat_vsa/` to demonstrate the red, then
restored — the landed tree keeps only the seam.

Mechanisms live in `src/cbat_vsa/cbat_backward.ml` (the inverse denote, the
deep walk, `constrain_edge`), `src/cbat_vsa/cbat_vsa.ml` (the fixpoint's
inline edge refinement, the seam), `src/cbat_vsa/cbat_ai_memmap.ml` (the cell merge),
`src/cbat_vsa/cbat_call_effects.ml` (the matched-pair SP restore), and
`src/hike_jump.ml` (the jcc/flag decoder).

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| BK-01 | L3a PLUS row: the walk's per-def producer subtraction through `operand_constraints`' PLUS arm met `{4}` into the `[RBP-8]` load cell. | In `cbat_backward.ml`'s `inverse_denote`, make the general `Bil.BinOp` `_` arm `env` (skip `operand_constraints`). | BK-01 (`bounded_above` false; cell stays top). |
| BK-02 | L3a MINUS row: the subtraction pre-image `[1,10]`. | As BK-01 (the same general BinOp arm). | BK-02. |
| BK-03 | L3a LSHIFT-const row: the shift pre-image `[0,9]` (40>>2). | Drop the shift arm's row (`| Bil.BinOp ((LSHIFT\|RSHIFT\|ARSHIFT), _, _) -> env`). | BK-03. |
| BK-04 | L3a TIMES over an unbounded operand is the identity (sound stop); the cell is TOP, never BOTTOM. | Invert the stop: make the TIMES arm return a bounded hull or bottom. | BK-04 (`is_top` false). |
| BK-05 | L3a NEQ guard is doubt: `cmp_inverse` leaves the env for NEQ. | Make the NEQ case walk the complement (`neq_complement`) instead of `env`. | BK-05 (`Ws.is_top` false). |
| BK-06 | L3c1-1 flag record: `Hike.Jump.compile_sub`'s `cross_guard`/`plan_block` recovers `CF := SLT(t,10)` from a bare `when CF`. | In `hike_jump.ml`, make `plan_block` return `[]` (no flag rewrite) so the guard stays `Bil.Var cf`. | BK-06 (cell stays top). |
| BK-07 | L3c1-2 a redefinition of the compared operand makes the guard constant-false; the taken edge is dead (`Ws.is_bottom`). | Make `read_def` position-insensitive (return the load def even when a later def redefines the operand). | BK-07 (cell is refined, not bottom). |
| BK-08 | L3c1-3 a non-comparison flag redefinition invalidates the record (`extract_facts` returns `None`). | Treat `Bil.Unknown` as a fact-producing rhs in `extract_facts`. | BK-08 (cell refines). |
| BK-09 | L3c1-4 multi-def base: the per-block producer subtraction yields the EXACT body-IN window `[1,10]`. | Run the walk raw: `walk_block ~raw:true` (skip the producer subtraction). | BK-09 (wider join; 11 ∈). |
| BK-11 | L3c2-1 `constraint_row` SLT gates on `provably_nonneg` (the seeded counter). | Force `provably_nonneg = false` in `constraint_row`. | BK-11 (two-piece row; `bounded_above … 3` false). |
| BK-12 | L3c2-2 the two-piece SLT total row for an unproven operand. | Drop the `total_row` fallback in `guard_row` for SLT (return `None`). | BK-12 (cell top). |
| BK-13 | L3c2-3 `c >= half` SLT/SLE single high interval. | Drop the `if c >= half` branch in `constraint_row`. | BK-13 (`l3c2_in_high` false). |
| BK-14 | L3c2-4 flag-indirected signed guard (record + signed row). | As BK-06 (`plan_block = []`). | BK-14. |
| BK-15 | L3c2-5 trace-exact cell refinement with no RBP prologue def (`constrain_cell_on_trace`). | Make `constrain_cell_on_trace` the identity (`fun ~env … -> env`). | BK-15. |
| BK-16 | L3c3-1 PLUS-HULL: the circular hull `{−1} ∪ [0,8]` on `t`. | As BK-01 (PLUS arm identity). | BK-16. |
| BK-18 | L3c3-2b seeded operand: the guard's signed row bounds `t`, so the exact TIMES slice applies. | Drop the TIMES slice in `operand_constraints` (return `None,None` for TIMES). | BK-18. |
| BK-19 | L3c3-3 RSHIFT-const row. | As BK-03 (drop the shift arms). | BK-19. |
| BK-20 | L3c3-4a ARSHIFT-const row with a provably non-negative operand. | Make the ARSHIFT arm consult `nonneg` and return identity when it holds. | BK-20. |
| BK-21 | L3c3-4b ARSHIFT on a top operand is a sound stop (identity). | Remove the non-negativity gate so ARSHIFT always refines. | BK-21 (`Ws.is_top` false). |
| BK-23 | L3c3-6 TIMES EQ non-divisible is the empty pre-image — the dead edge prunes, so the cell is BOTTOM. | Invert the divisibility check so the row is non-empty. | BK-23 (`is_bottom` false). |
| BK-24 | L3c4-1 Var-vs-Var LT: `overlap_constraints` caps `t` at `u`'s max. | Make `overlap_constraints` the identity (`fun _ _ _ -> None,None`). | BK-24. |
| BK-25 | L3c4-2 a TOP Var-vs-Var operand makes the refinement vacuous; the cell is an unbounded ray, never BOTTOM. | Force `overlap_constraints` to emit `[0,c]` even when an operand is top. | BK-25 (`is_bottom` true, or `bounded_above … 1000`). |
| BK-26 | L3c4-3 DIVIDE-const row. | Drop the DIVIDE arm in `inverse_denote` (identity). | BK-26. |
| BK-27 | L3c4-4 HIGH-extract producer row (`high_cast_constraint`). | Make `high_cast_constraint` return `None`. | BK-27. |
| BK-28 | L3c4-5 DIVIDE k = 0 is a sound stop (identity); the cell is TOP. | Remove the k=0 guard so DIVIDE 0 refines. | BK-28 (`is_top` false). |
| BK-29 | L3c5-1 const-first EQ normalizes to const-second (`cmp_inverse`'s `Bil.Int c0, e0` arm). | Drop the const-first arm in `cmp_inverse` (`| Bil.Int _, _ -> env`). | BK-29. |
| BK-30 | L3c5-2 MOD has no closed form — identity; the cell is TOP. | Remove the MOD identity arm and add a row. | BK-30 (`is_top` false). |
| BK-31 | L3c5-3a AND-identity row (`t AND ~0 ≡ t`). | Drop the AND/OR identity rows in `inverse_denote`. | BK-31. |
| BK-33 | L3c5-4 an Unknown condition keeps the env unchanged (never asserts). | Make `inverse_denote`'s `Bil.Unknown` arm return `AI.bottom`. | BK-33 (`AI.equal` false). |
| BK-35 | L-3b partition: the iterate view vs the exit view hold different cells. | Drop the trace-taken view (union the body IN state with the exit state). | BK-35 (exit cell loses `{8}` / iterate cell top). |
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
| BK-47 | R2-1 inline-arithmetic condition `(t+1) < 64`: the producer recursion yields the 64-element hull (cardinality compared numerically). | Drop the inline-BinOp fallthrough in `constrain_def_chain`/`cmp_inverse`. | BK-47 (cardn > 64 / top). |
| BK-48 | R2-2 NOT-of-comparison: the NOT-edge keeps its env (the false-edge row never confines the taken edge); the seeded taken value 8 survives. | Make the `has0` arm apply the false-edge row to the taken edge. | BK-48 (`8 ∈` false, or `bounded_above … 4`). |
| BK-49 | R2-3 const-first LT flip dispatches UGT (`10 < t` → `[11, 2^w)`). | Drop `flip_guard_op` for the const-first arm. | BK-49. |
| BK-50 | R2-4 nested TIMES chain: the exact no-wrap slice yields the body-IN singleton `{63}`. | Drop the TIMES no-wrap slice. | BK-50 (`Ws.equal` false). |
| BK-51 | M5-1 the MINUS wrap hull `{0xFFFFFFFF, 0..3}` (cardinality 5, compared numerically). | Make the wrap hull return the unwrapped interval only. | BK-51 (cardn ≠ 5). |
| BK-52 | M5-2 TIMES k=0 identity. | As BK-22. | BK-52 (`Ws.is_top` false). |
| BK-53 | M5-3 XOR-~0 bijection `{~5}`. | Drop the XOR/lnot bijection row. | BK-53. |
| BK-54 | M5-4 LOW cast in the walk: truncation hull `[5, 0xFFFFFF05]`. | Make `low_cast_constraint` return `None`. | BK-54. |
| BK-55 | M5-5 signed-division rule `{−6,−5}`. | Drop the SDIVIDE arm. | BK-55. |
| BK-56 | M5-6 Var-identity row propagates through the copy (`≤ [0,9]`, not `[0,10]`). | Drop the `Bil.Var` identity propagation in the walk. | BK-56 (`bounded_above … 9` false). |
| BK-57 | T1 the RSP-based same-block cell meet (`constrain_cell_on_trace` meets `[RSP-8]` into the offset key). | Make `constrain_cell_on_trace` the identity. | BK-57 (cell unchanged; `15 ∈`). |
| BK-58 | S6: a dynamic-index read spans several cells, so the read's value constraint is not met into each — the cells keep their stored values (the join ruling is a join law, not a meet law; ADR 0025's amendment) | drop the S6 gate in `cbat_backward.ml`'s `backward_cell_keys` (meet every `bounded_cell_key`) | the cell at 0 narrows (15 ∉), inverting the pin |
| BK-59 | S6: a ranged read that only partly overlaps a stored cell is not met into it — the cell keeps its stored value | as BK-58 (meet every key) | the cell at 0 narrows (15 ∉) |
| BK-60 | S6: the dynamic-index read meets no cell — the cells at 0, 40 and 80 all keep their stored values | as BK-58 (meet every key) | the cells at 0/40/80 narrow (15 ∉) |
| BK-71 | S11 the NEG row (`neg` of the produced window). | Drop the `Bil.NEG` arm. | BK-71. |
| BK-74 | S15b the SIGNED-ext pre-image `[0,0xFF]`; the empty meet keeps the env value (identity). | Make the empty meet narrow/pick the constraint. | BK-74 (`Ws.equal` false). |
| BK-75 | S16a `complete_cond` negates each of the six comparisons structurally (both orders). | As BK-70. | BK-75. |
| BK-76 | S16b the completed fallthrough of `(x <u y)` seeds `y ⊆ [0,3]`. | As BK-70. | BK-76. |
| BK-77 | S16c the 3-comparison AND chain narrows `a` to `[0,6]` and leaves `y`,`c`. | Make the `Bil.BinOp (AND, …)` `{1}` arm identity. | BK-77. |
| BK-78 | S14 an infeasible constant is `AI.bottom`; a consistent one is the identity. | Make `inverse_denote`'s `Bil.Int` arm always `env`. | BK-78 (bottom check false). |
| BK-80 | S18 Ite with a singleton true condition constrains only the true branch. | Constrain both branch operands. | BK-80 (`u` narrowed). |
| BK-81 | S19 Ite with an unknown condition keeps both branches. | Constrain both branch operands. | BK-81 (`t`/`u` narrowed). |
| BK-83 | S21 the AND singleton mask keeps the mask's bits from the constraint and frees the rest (hull `[0x30, 0xFFFFFF3F]`). | Make the general-mask AND arm identity. | BK-83 (`0x30 ∈` false). |
| BK-84 | the low cast of a zero-extended narrow value: `low:32[pad:64[x]]` collapses to `x`, so the constraint `[0,0xF]` narrows `x` to `[0,0xF]`, not the truncation hull. | Drop the widening arm so `low_cast_constraint` always takes the wide hull. | BK-84 (`x` stays `[0,2^32-1]`; `max_elem` is not `0xF`). |
| BK-85 | the var-var signed guard reads its bound's payload: `SLT(low:32[x], y)` with `y = {4}` (a signed extremum) takes the unsigned window `[0,3]` when `x`'s low half is provably non-negative, so the low-cast pre-image drops the value whose low half is `0x10`. | Compare `c` with `half` through its signed flag (`Cbat_word.(>=) c half`) in `evidence_constraint`'s SLT/SLE arms. | BK-85 (`out ∈ x`; the wrapped reading's pre-image is top). |
| BK-86 | the collapsed seeding rule: `cond_seeds` answers every bounded free var of the cond (a guard the analysis already satisfies still seeds), so `refine_edge_inline` runs the walk and the flag-indirected loop's body-IN cell at RBP-8 stays bounded. | Make `cond_seeds` return `Var.Set.empty` — the empty-seeds bail in `refine_edge_inline` then skips the walk. | BK-86 (cell unbounded; the seeding rule carries 42 backward pins red together). |
| BK-95 | the replay's write sites skip what changes nothing: `meet_word` writes a def's output fact or a block input fact only when it `strictly_precedes` the replayed value, counted per site (`Output_write`/`Input_write`) by `refine_edge_count_writes`. The load's read fact already narrows x, so both output facts are equal (0 writes); in the second fixture x's leftover and the seed u's `[2,5]` each narrow the entry (2 writes). | Remove `&& strictly_precedes m cur` in `meet_word` (the equal output facts then write). | BK-95.output-equal (the count rises to 2). |
| BK-96 | the collapsed seed's delivery: `refine_edge` takes seed VARS and the walk reads each seed's constraint from the state it walks, so an unconsumed seed keeps the walked env's own value while the guard's row still reaches its operand. | Restore the pre-`33edbf8b` seam shape — `(var, constraint)` pairs folded into the walked env with `AI.add_word` before walking — and pass the unconsumed seed a folded `[0,1]` against its env value `[2,5]`; the seed then delivers the folded value. | BK-96.env-value (u delivers `[0,1]`; `BK-96.delivered` stays green, so the red is the fold alone). |
| BK-100 | a var rewritten after the def that receives the guard's constraint keeps its edge value: the edge state is the block replayed forward, so the later `y := u` decides edge y. | Write each output fact straight into the edge state (HEAD's `confine`). | BK-100.rewritten-kept (edge y loses 50). |
| BK-101 | a cell stored after the load the guard reads keeps its edge value: the read fact holds at the load's position and the replayed later store decides the edge cell. | Meet the read fact into the edge memory (HEAD's `call_env` edge memory + `commit`). | BK-101.rewritten-kept (the edge cell loses 50). |
| BK-102 | a store's cell takes its data's constraint: the replayed store writes the output-refined x, so clang -O0's spilled switch index is bounded at the edge. | Drop the output facts from the replay (replay from the inputs only). | BK-102 (the edge cell is unbounded). |
| BK-103 | a cell overwritten later takes nothing from the earlier store's data: the replayed later store decides the edge cell. | Meet each store's refined data into the edge memory regardless of later stores. | BK-103 (the edge cell loses 50). |
| BK-104 | a load's address narrows to the slots whose contents can produce the guarded value: `load_address_constraint` bisects the address set over known memory (image words here) and the address inverse bounds i by the surviving slots' hull. | Return `None` from `load_address_constraint`. | BK-104.dropped (i keeps 3). |
| BK-105 | T27 step 4: cell coverage is element-level — a strided piece whose span crosses a cell but whose elements never read it is not covered; an element on the cell's bytes (or a read reaching in from below) is. | Use `Mem.has_cell_in` as the decision (restore the span rule) instead of the element-level `piece_touches_cell_bounds`. | by review: the span rule re-splits an uncovered piece, inverting the pinned shape (2026-10-14). |
| BK-106 | T27 step 4: image coverage is element-level — the whole read must fit (a dense piece starting past the fit range is not covered), and a strided piece is tested on its own grid, not its span. | Restore a span-overlap test in `piece_touches_image_bounds`. | by review: the span test claims coverage for a piece whose elements miss the fit range (2026-10-14). |
| BK-107 | T27 step 4b: a dense multi-element address run partitions in one decision (`Parts`) — the image reads that miss the guard value drop on both sides of the kept address (8 kept; 0 and 15 dropped). | Make the partition return `Split` instead of `Parts`. | by review: the bisection re-splits the run and the one-decision shape inverts (2026-10-14). |
| BK-108 | T27 step 4: a same-line cell whose hull starts below nb-1 keeps the wrapped read-start range `[cl-(nb-1), ch]` semantics — the bulk (Clp) result restricted to the small set equals the per-singleton (Exact-tier) result. | Drop the `-(nb-1)` back-shift in `piece_touches_cell_bounds`. | observed FAIL at `BK-108.read-reaches-in` (expected true, got false) under that inversion (2026-10-14). |
| BK-109 | the AND-mask pre-image of `x land k <= vhi` keeps every satisfying `x`: the upper bound is the largest submask of `k` at most `vhi` with every unmasked bit set (`(x&1)<=2` keeps `0xff`; `(x&5)<=2` keeps `0xfb`, drops `0xfc`) | restore the `vhi lor lnot k` bound in `operand_constraints` | `0xff` is dropped from `(x&1)<=2` |
| BK-110 | `~(a \| b)`: `complete_cond` pushes NOT through OR (De Morgan), and the `constrain_operands` OR=false row constrains both operands — an edge `~(CF \| ZF)` drives CF and ZF to `{0}` on both the pushed and the raw form | restore `negated_cond`'s `_ -> Bil.UnOp (Bil.NOT, e)` for OR and drop the OR=false row | CF and ZF stay `{0,1}` (no refinement) |
| BK-111 | a seedless observer (disabled cond with no constrained var) skips the walk and builds no def-prefix chain; a cond bounding a var does | drop the empty-seed guard in `acquire_unsat` | `BK-111.seedless` FAILs (the prefix chain is cached) |
| BK-87 | A4 table — syntactic `x` cast-UNSIGNED: the compared var is defined by `Cast(UNSIGNED,64,t)`; the exit edge stays live and the head cell keeps the cast's reachable values. | textually invert the pinned contract in `test/unit/test_backward.ml` | pin FAILs under that inversion (re-demonstrated by review) |
| BK-88 | A4 table — syntactic `x` extract-hull: the compared var is `Extract(31,16,t)` (the top half-word); the exit edge stays live. | textually invert the pinned contract in `test/unit/test_backward.ml` | pin FAILs under that inversion (re-demonstrated by review) |
| BK-89 | A4 table — range `x` cast-UNSIGNED: the guard's operand is `Cast(UNSIGNED,64,t)`. | textually invert the pinned contract in `test/unit/test_backward.ml` | pin FAILs under that inversion (re-demonstrated by review) |
| BK-90 | A4 table — range `x` extract-hull: the guard's operand is `Extract(31,16,t)`. | textually invert the pinned contract in `test/unit/test_backward.ml` | pin FAILs under that inversion (re-demonstrated by review) |
| BK-91 | A4 candidate — the wrapping `cur` `[0xFFFFFFF0, 0x10]` has unsigned max `0x10 < 2^31`, so the `SLT` evidence row `[0,4]` drops the reachable value. | textually invert the pinned contract in `test/unit/test_backward.ml` | pin FAILs under that inversion (re-demonstrated by review) |
| BK-92 | A4 loop — a wrapping counter (seeded `0xFFFFFFFE`, `+1`, guard `SLT(t,2)`): the reachable head values are `{0xFFFFFFFE, 0xFFFFFFFF, 0, 1, 2}`. | textually invert the pinned contract in `test/unit/test_backward.ml` | pin FAILs under that inversion (re-demonstrated by review) |
| BK-93 | A4 table — the BASE cell (no cast/extract): the guard compares the loaded var directly. | textually invert the pinned contract in `test/unit/test_backward.ml` | pin FAILs under that inversion (re-demonstrated by review) |
| BK-94 | the extract constraint — `Extract(15,0,x)` constrained to `[0,3]`: the operand constraint is `[0, 0xFFFF0003]`. | textually invert the pinned contract in `test/unit/test_backward.ml` | pin FAILs under that inversion (re-demonstrated by review) |
| BK-97 | the low-cast guard window reads the operand's reachable set — `SLT(low:32[x], 8)` over `x = {0..9}` gives `{0..7}` (the wide hull would never bound a counter). | textually invert the pinned contract in `test/unit/test_backward.ml` | pin FAILs under that inversion (re-demonstrated by review) |
| BK-98 | the nested-load increment store (`mem[c] := mem[c] + 1`) inside the walked head block bounds the guard's counter cell. | textually invert the pinned contract in `test/unit/test_backward.ml` | pin FAILs under that inversion (re-demonstrated by review) |
| BK-99 | the def-carried increment (`v := t + 1; mem[c] := v`) in the walked head block bounds the same counter cell (the BK-98 control). | textually invert the pinned contract in `test/unit/test_backward.ml` | pin FAILs under that inversion (re-demonstrated by review) |
