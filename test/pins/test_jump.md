# Pins — test_jump

Module: `test/unit/test_jump.ml` (group `jump`, ids `JMP-01`…`JMP-51`),
migrating `test_cbat/test_jump.ml`.  Production mechanism:
`src/hike_jump.ml` (`Hike.Jump.compile_sub`, target-driven by the
`jump_target` flag-role target in `test/unit/fixtures.ml`, which declares
ZF/CF/SF/OF/PF).

The compiler walks each jump's block backward — and on into a unique goto
predecessor — substituting every def it passes into the cond and
simplifying after each step.  The smallest flag-free form wins (ties: one
inlinable at the jump, then the latest); it is inlined when its vars hold
the same values at the jump, else bound to a fresh comparison def at its
own position.  No flag-free form leaves the cond unchanged.

There is no `Test_seam` for this pass, so no switch can be flipped from
the test tier.  The disable recipes below are textual and name the source
site to break.  Every pin builds its own fixture inside its closure — no
cross-pin state.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| JMP-27 | A test group with no OF def leaves OF in the substituted cond; `acceptable` refuses a form that still reads a flag, so the cond is unchanged. | In `acceptable`, drop the flag check. | the cond becomes the half-substituted xor over OF. |
| JMP-30 | `rewrite` rebuilds an equality's zero at the compared operand's width and folds `(x − y) = 0` to `x = y`, so a 32-bit compare renders `EQ x32 y32`. | Drop the `EQ (MINUS (a, b), 0)` rule in `rewrite`. | the cond stays `x32 − y32 = 0`. |
| JMP-32 | `compile_sub` rewrites conds only; block count and `Goto (Direct …)` targets are intact. | In `compile_sub`, rebuild a rewritten jmp as `Goto (Direct (Tid.create ()))`. | targets lost. |
| JMP-35 | A block with two predecessors ends the walk (`unique_goto_pred`), so a flag defined differently on each path is never substituted. | In `unique_goto_pred`, return the first predecessor of several. | the cond compiles from one arbitrary path's ZF. |
| JMP-36 | `acceptable` refuses a form containing `Unknown`. | In `acceptable`, drop the `has_unknown` check. | the cond becomes `unknown[bits]`. |
| JMP-37 | Relations over different operand pairs do not combine (`combine` needs one pair in either orientation): an inconsistent `jbe` compiles to the substituted `x <u y \| x = 0`, and the dead flag defs drop. | In `combine`, accept any two pairs. | the cond becomes a single relation over the wrong pair. |
| JMP-38 | A flag no def in the block or a unique goto predecessor writes stays in the cond, so `acceptable` refuses every form (the inc/dec class: CF preserved). | In `acceptable`, drop the flag check. | the cond keeps CF beside the substituted ZF. |
| JMP-39 | An unchanged jump consumes nothing, so no def is dropped. | Make `compile_sub` drop every flag def it passes. | the two defs drop. |
| JMP-40 | The backward walk meets the LAST def of a var first and substitutes it; the earlier def is never reached for that var. | Walk the defs in block order in `compile_jmp`. | the cond reads the first ZF def's `x`. |
| JMP-42 | A cond with no free vars is not walked. | Remove the free-vars check in `compile_jmp`. | (shape-only: the constant cond is left equal either way.) |
| JMP-43 | No jump changes, so no def is consumed or dropped. | In `compile_sub`, drop every flag def regardless of plans. | the five cmp defs drop. |
| JMP-44 | `CF := 1` substitutes to the constant-true cond; CF is consumed and its def dies. | Drop the constant-cond acceptance (refuse closed forms in `acceptable`). | the cond stays `CF`, the def survives. |
| JMP-45 | `cmp x, 0`'s folded OF `x & (x ^ t)` with `t := x`: substituting `t` folds the overflow to 0 (`x ^ x`, `x & 0`, `0 <s 0`), the xor core reduces to the sign, and `ZF \| SF` combines to `x <=s 0`. | Drop the `XOR (a, a) → 0` rule in `rewrite`. | the cond stays the uncollapsed xor over the overflow term. |
| JMP-46 | Clang -O0's reused register: `x` is written three times, so the borrow and the zero test read different `x`'s; substitution is positional, so the smallest form is `6 <u x` read where `t := x` reads it, bound to a fresh comparison def inserted before that def (x is rewritten before the jump). | Make `subst` stop at the first def of a var already substituted (position-blind resolution). | the cond stays `~(CF \| ZF)`. |
| JMP-47 | The signed `jle` over a register rewritten after the compare: `y <=s z` (the earliest equal-size form) is preferred because it is inlinable at the jump. | In `order`, drop the inline component. | a comparison def is inserted for `x <=s z`. |
| JMP-48 | `cmp` in a block and `jbe` in its goto successor: the walk continues into the unique goto predecessor; the flags die. | Return `None` from `unique_goto_pred`. | the cond stays `CF \| ZF`. |
| JMP-49 | `jp` after `ucomisd`: the lifter's PF is `is_nan(a) \| is_nan(b)` over intrinsic results, defined in the predecessor block; the cond compiles to that unordered test. | Drop `parity_flag` from `flag_vars`. | the cond stays `PF` (PF is then not a flag, and the original `PF` is already acceptable). |
| JMP-50 | Integer `jp`: PF is the low byte's parity of the result; the cond becomes that expression and the PF def dies. | Drop `parity_flag` from `flag_vars`. | the cond stays `PF`. |
| JMP-51 | A call edge ends the walk (`preds_of` marks it `Other_edge`): the callee may write the flags, so a ZF set before the call never reaches the jump after it.  The pre-substitution compiler compiled this shape. | Mark call-return edges `Goto_edge` in `preds_of`. | the cond becomes `x = 0` across the call. |
