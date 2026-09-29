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

The red-evidence cells below state the expected failure mode; the recipes
are textual (the mechanism is not runtime-switchable at the pin), so no
measured red is claimed here.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| JMP-27 | `signed_item` needs an SF and either the xor-core OF triple or the and-form `OF ≡ 0`; a missing OF def leaves no fact → the identity (`parse_bexp`/`eval_bexp` residual). | In `signed_item`, add a `| None, _ -> Some (Rel (LT, true, xv, yv))` arm that fabricates the signed ordering without OF. | to be recorded |
| JMP-30 | `zero_exp` builds the zero at the compared operand's own width, so a 32-bit `x32−y32` renders 32-bit `EQ x32 y32`. | In `zero_exp`, always return `Word.zero 64` regardless of `e`'s width. | to be recorded |
| JMP-32 | `compile_sub`'s `Term.map blk_t` / `Term.map jmp_t` rewrite preserves the CFG (block count and `Goto (Direct …)` targets intact). | In `compile_sub`, rebuild a rewritten jmp's kind as an unconditional `Goto (Direct (Tid.create ()))`. | to be recorded |
| JMP-35 | Ambiguous reaching defs (several predecessors) enter `rm`, so `flag_def` finds no candidate → residual. | In `flag_def`'s reaching arm, take `List.hd` of the ambiguous candidates instead of requiring a singleton. | to be recorded |
| JMP-36 | `parse_bexp` returns `None` for a non-bexp cond (`PF:unknown`), leaving the jmp residual. | In `parse_bexp`, make the catch-all return `Some (V pf)` for an `Unknown`. | to be recorded |
| JMP-37 | The consistency checks (`is_minus_xy`, `same_exp`) refuse a `jbe` whose ZF subtraction and CF borrow disagree → residual. | In `combine`, drop the `same_exp c p1 p2 && same_exp c q1 q2` pair-agreement guard. | to be recorded |
| JMP-38 | The inc/dec class: no CF def in the block gives `facts.cf = None`, so a CF-consuming `jbe` has no atom → residual. | In `flag_item`, default a missing CF fact to the constant-false `Rel (EQ, false, x, x)`. | to be recorded |
| JMP-39 | A residual (unchanged) block drops no defs — `plan_block.changed` false means `consumed_vars` is empty and the block is returned whole. | In `plan_block`, set `consumed_vars` unconditionally from `i.flags` regardless of `changed`. | to be recorded |
| JMP-40 | Within one block the LAST def of a flag is the reaching one (all defs precede all jmps; the first is a dead write) — the second ZF def's `yv` comparison emits. | In `plan_block`, build `flag_map`/`rhs` with the FIRST def per var (`Core.Map.set` only when absent). | to be recorded |
| JMP-42 | An unconditional jump cond (`Int 1`) is not a bexp — `parse_bexp` returns `None` and the cond is untouched. | In `plan_block`, default a failed `parse_bexp` to a compiled constant. | to be recorded |
| JMP-43 | No `Int`-cond def family is consumed, so all five cmp defs survive. | In `plan_block`, set `changed = true` unconditionally (consuming flag defs for the `Int 1` cond). | to be recorded |
| JMP-44 | `CF := 1` is the const-true flag fact: a `jb` over it compiles to the const-true branch and the CF def dies. | Drop the `CF, e when is_one_int e` arm in `extract_facts`. | JMP-44 red: the cond stays `Var CF` and the def survives. |
