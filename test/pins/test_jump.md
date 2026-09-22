# Pins — test_jump

Module: `test/unit/test_jump.ml` (group `jump`, ids `JMP-01`…`JMP-43`),
migrating `test_cbat/test_jump.ml`.  Every source `check` site is carried as
one pin; none retired.  Production mechanism: `src/hike_jump.ml`
(`Hike.Jump.compile_sub`, target-driven by the `jump_target` flag-role
target in `test/unit/fixtures.ml`).

There is no `Test_seam` for this pass, so no fail-before switch can be
flipped from the test tier.  Production `src/` is never modified.  The
disable recipes below are textual and name the source site to break; the
recorded red is the state that recipe produces (re-demonstrated whenever
the cited mechanism changes).  Every pin builds its own fixture inside its
closure — no cross-pin state.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| JMP-01 | `zf_item` resolves an inline `(x−y)` ZF and renders `EQ x y` (operand resolution, not re-substitution). | In `zf_item`, replace the `Bil.BinOp (Bil.MINUS, x, y)` arm with the non-minus `zero_exp` arm (`Bil.BinOp (Bil.EQ, xv, W0)`). | to be recorded |
| JMP-02 | `compile_sub` drops every def of a consumed ZF var once its only use was the rewritten jump. | In `compile_sub`, make the consumed-drop a no-op (`let drop_consumed sub _ = sub`). | to be recorded |
| JMP-03 | `zf_item`'s non-minus arm compares `d` to zero at `d`'s OWN width (the `0 = t` reuse form renders `t != 0`, never re-substituting `t`). | In `zf_item`, replace the `Zconst`/`zero_exp d` arm with `None`. | to be recorded |
| JMP-04 | Same consumed-ZF drop as JMP-02 (reuse form). | `let drop_consumed sub _ = sub`. | to be recorded |
| JMP-05 | A reused value var (`t`, not a flag) is never in `consumed_vars` — only flag vars drop. | In `plan_block`, extend `consumed_vars` to every var in `i.flags`'s resolved exps. | to be recorded |
| JMP-06 | `flag_item`/`extract_facts` map `CF := a <u b` to `Rel (LT, false, a, b)` and render `a <u b` verbatim. | In `extract_facts`, make the `CF, Bil.BinOp (Bil.LT, …)` arm return `None`. | to be recorded |
| JMP-07 | Consumed-CF drop (JMP-02 mechanism). | `let drop_consumed sub _ = sub`. | to be recorded |
| JMP-08 | The ADD-carry shape `CF := t <u x` is the same `Ult` fact — rendered verbatim as `t <u x`. | `extract_facts` `CF, LT` arm returns `None`. | to be recorded |
| JMP-09 | Consumed-CF drop on the add-carry form. | `let drop_consumed sub _ = sub`. | to be recorded |
| JMP-10 | The non-flag sum def `t` survives (only consumed flag vars drop). | In `plan_block`, extend `consumed_vars` to non-flag operand vars. | to be recorded |
| JMP-11 | `complement_item` + `render_atom`: `jae` = NOT(CF) flips `LT`→`GE`, and `GE` renders operand-swapped `y <=u x` (no NOT survives). | In `render_atom`, render `GE` as `NOT (b <u a)` instead of `b <=u a`. | to be recorded |
| JMP-12 | `combine`'s relation lattice on the shared `(x,y)` pair folds `CF OR ZF` to `LE x y`. | In `combine`, return `None` for two `Rel` atoms whose bits fully agree (`rel_of_bits` result `LE`). | to be recorded |
| JMP-13 | Both consumed flags (`CF` AND `ZF`) drop after the OR-join rewrite. | `let drop_consumed sub _ = sub`. | to be recorded |
| JMP-14 | `ja` = NOT(CF OR ZF) → complement of `LE` is `GT`, rendered `y <u x`. | In `rel_complement`, map `LE -> GE` (identity on the OR result). | to be recorded |
| JMP-15 | `signed_item`'s xor-core arm fires only when the OF diff resolves to `(x−y)` AND the sign exp equals that diff → `SLT x y`. | In `signed_item`, drop the `is_minus_xy c d x y && same_exp c e d` guard. | to be recorded |
| JMP-16 | `combine` ORs the ZF equality atom with the signed `LT` atom on the shared pair → `LE x y` (signed flavor from the ordering side). | In `combine`, reject a pair whose two atoms mix `EQ` and a signed ordering (the `eq r1 || eq r2` arm returns `None`). | to be recorded |
| JMP-17 | `jg` = NOT(zf OR core) → `SLE` complement → operand-swapped `SLT y x`. | In `render_atom`, render `GT` without the operand swap. | to be recorded |
| JMP-18 | `jge` = NOT(core) → `GE` → `SLE y x`. | In `render_atom`, render `GE` without the operand swap. | to be recorded |
| JMP-19 | `zf_item`'s non-minus arm compares the `AND` exp to zero (the conjunction kept, constant-right). | In `zf_item`, drop the non-minus `zero_exp` arm (return `None`). | to be recorded |
| JMP-20 | The test/and group: `extract_facts`'s `OF, is_zero_int` arm sets `and_form`, and `signed_item`'s `and_form` arm makes SF alone the sign → `SLT (x&y) 0`. | In `extract_facts`, make the `OF, e when is_zero_int e` arm return `None` (group not detected). | to be recorded |
| JMP-21 | The and-group's consumed `SF` and `OF` defs both drop. | `let drop_consumed sub _ = sub`. | to be recorded |
| JMP-22 | `test jle` ORs ZF with the and-form sign core → `SLE (x&y) 0`. | In `combine`, reject the `Const`/`Rel` or `EQ`/signed mix on the and-group pair. | to be recorded |
| JMP-23 | `test jg` = NOT(`test_jle_cond`) → `SLE` complement → `SLT 0 (x&y)`. | In `rel_complement`, map `LE -> GE`. | to be recorded |
| JMP-24 | `test jge` = NOT(`test_jl_cond`) → `LT` complement → `SLE 0 (x&y)`. | In `rel_complement`, map `LT -> GE`. | to be recorded |
| JMP-25 | `test je` with the full flag group renders `EQ (x&y) 0`. | In `zf_item`, drop the non-minus `zero_exp` arm. | to be recorded |
| JMP-26 | `test jne` = NOT(ZF) → `NEQ (x&y) 0`. | In `complement_item`, make `EQ`/`NEQ` complement the identity. | to be recorded |
| JMP-27 | `signed_item` needs an SF and either the xor-core OF triple or the and-form `OF ≡ 0`; a missing OF def leaves no fact → the identity (`parse_bexp`/`eval_bexp` residual). | In `signed_item`, add a `| None, _ -> Some (Rel (LT, true, xv, yv))` arm that fabricates the signed ordering without OF. | to be recorded |
| JMP-28 | `zf_item` folds `(x − 0) = 0` to `EQ x 0`; `jnz` complements to `NEQ x 0`. | In `zf_item`'s minus arm, map `is_zero_int x` to `Rel (EQ, false, x, x)` (no fold). | to be recorded |
| JMP-29 | `zf_item` folds `a−a` to `Const true`; `jz` renders the 1-bit true constant. | In `zf_item`'s minus arm, drop the `Exp.equal x y -> Const true` case. | to be recorded |
| JMP-30 | `zero_exp` builds the zero at the compared operand's own width, so a 32-bit `x32−y32` renders 32-bit `EQ x32 y32`. | In `zero_exp`, always return `Word.zero 64` regardless of `e`'s width. | to be recorded |
| JMP-31 | `plan_block` maps EVERY jmp of a block through the fact algebra (both jmps of a shared block compile). | In `plan_block`, map only the first jmp: `List.mapi` with `if i > 0 then (j, None, None)`. | to be recorded |
| JMP-32 | `compile_sub`'s `Term.map blk_t` / `Term.map jmp_t` rewrite preserves the CFG (block count and `Goto (Direct …)` targets intact). | In `compile_sub`, rebuild a rewritten jmp's kind as an unconditional `Goto (Direct (Tid.create ()))`. | to be recorded |
| JMP-33 | `reaching_defs` carries the unique reaching flag def from a single predecessor into the successor's `in_state.ru`; `flag_def`'s reaching arm serves the facts. | In `flag_def`, drop the `[]`/reaching arm so only same-block facts count. | to be recorded |
| JMP-34 | `compile_sub` drops a consumed flag def sub-wide (`uses_of` proves no other use), including a predecessor-block def. | In `uses_of`, union the consumed vars into `uses_of` so the drop guard sees the var as still-used. | to be recorded |
| JMP-35 | Ambiguous reaching defs (several predecessors) enter `rm`, so `flag_def` finds no candidate → residual. | In `flag_def`'s reaching arm, take `List.hd` of the ambiguous candidates instead of requiring a singleton. | to be recorded |
| JMP-36 | `parse_bexp` returns `None` for a non-bexp cond (`PF:unknown`), leaving the jmp residual. | In `parse_bexp`, make the catch-all return `Some (V pf)` for an `Unknown`. | to be recorded |
| JMP-37 | The consistency checks (`is_minus_xy`, `same_exp`) refuse a `jbe` whose ZF subtraction and CF borrow disagree → residual. | In `combine`, drop the `same_exp c p1 p2 && same_exp c q1 q2` pair-agreement guard. | to be recorded |
| JMP-38 | The inc/dec class: no CF def in the block gives `facts.cf = None`, so a CF-consuming `jbe` has no atom → residual. | In `flag_item`, default a missing CF fact to the constant-false `Rel (EQ, false, x, x)`. | to be recorded |
| JMP-39 | A residual (unchanged) block drops no defs — `plan_block.changed` false means `consumed_vars` is empty and the block is returned whole. | In `plan_block`, set `consumed_vars` unconditionally from `i.flags` regardless of `changed`. | to be recorded |
| JMP-40 | Within one block the LAST def of a flag is the reaching one (all defs precede all jmps; the first is a dead write) — the second ZF def's `yv` comparison emits. | In `plan_block`, build `flag_map`/`rhs` with the FIRST def per var (`Core.Map.set` only when absent). | to be recorded |
| JMP-41 | Both same-block ZF defs drop after the rewrite (the var is unused sub-wide). | `let drop_consumed sub _ = sub`. | to be recorded |
| JMP-42 | An unconditional jump cond (`Int 1`) is not a bexp — `parse_bexp` returns `None` and the cond is untouched. | In `plan_block`, default a failed `parse_bexp` to a compiled constant. | to be recorded |
| JMP-43 | No `Int`-cond def family is consumed, so all five cmp defs survive. | In `plan_block`, set `changed = true` unconditionally (consuming flag defs for the `Int 1` cond). | to be recorded |
