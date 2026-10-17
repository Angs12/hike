# test_model pins

Module `test/unit/test_model.ml` (ids `MOD-10`..`MOD-45`), migrating
`test_cbat/test_model.ml`.  Every source `check`/`check_bound` site is carried
as one pin, in source order across the six entry points
(`run_producer_record`, `run_layout`, `run_stl_rewrite`, `run_emitter_shapes`,
`run_text`, `run_abi_and_kb`); none retired.  Mechanism: the producer record
(the composed fixpoint), the layout from the finalized
tree, stack-to-locals fission, the emitter's alloca shapes, the printable-run
rule, and the Abi/Kb convention facts.

The mechanisms are not Test_seam-switchable, so — per the lane spec
`§Fail-before` — the disable recipes below are textual (production `src/` is
never touched) and the red is re-demonstrated by review when the mechanism
changes.  Each recipe names the pins it turns red; no measured red is claimed
here.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| MOD-10 | A plain-TOP identity member forces the residue region (id 0) and sets `runtime_residue`. | In `layout_of_tree`, drop the `member_runtime` flag. | MOD-10. |
| MOD-17 | Write-closed Window: an Args cell that also contains a store takes Window storage on both sides (the read keeps its mem node and tag, never a slot). | In `conversion_of` (l.116), treat a stored Args cell as an `Arg_slot`. | MOD-17. |
| MOD-18 | `Hike_split_mem.normalize` splits the RMW; write-closure demotes the slot for both sides, so every memory node is on `window_mem`. | In `src/hike_split_mem.ml`, skip the split; or convert the hoisted read to a slot in the rewrite. | MOD-18. |
| MOD-19 | `Hike_jump.compile_sub` compiles flag idioms to value comparisons — no memory node rides a cond. | In `src/hike_jump.ml`, `compile_sub` returns the sub unchanged. | MOD-19. |
| MOD-20 | The load def converts to the region mem and the guard reads its converted temp transitively. | As MOD-12. | MOD-20. |
| MOD-33 | `Hike_abi.is_sp` / `sp`: the stack pointer is the target's stack-pointer register, and only it; the frame pointer is not the stack pointer (SP-only, ADR 0008). | In `hike_abi.ml`, make `is_sp` true for the frame pointer. | MOD-33. |
| MOD-34 | The frame pointer and the arithmetic flags come from the target's register roles (`Abi.frame_pointer`, `zero_flag`, `carry_flag`, `sign_flag`, `overflow_flag`, `parity_flag`) on BAP's declared x86-64 target; a target without a role fails the lookup; the frame pointer is an ordinary callee-saved register. | In `hike_abi.ml`, read the SysV name instead of the role (`by_role`), return a fallback instead of failing, or drop the frame pointer from `callee_saved`. | MOD-34 (role registers, failing lookup, callee-saved checks). |
| MOD-37 | An unknown target falls back to the SysV record (`of_target` total; `addr_size_bits unknown = 0`). | In `hike_abi.ml`, make `of_target` raise on unknown, or return a nonzero `addr_size_bits`. | MOD-37. |
| MOD-38 | BAP's x86-64 target reifies the SysV stack pointer as the SP. | In `hike_abi.ml`, make `of_target` skip the target SP reification. | MOD-38. |
| MOD-39 | The x86-64 word is 8 bytes, in the SysV record and in `of_target`'s. | In `hike_abi.ml`, hardcode the `word` field to a wrong value. | MOD-39. |
| MOD-40 | The ONE caller-window denotation (`Hike_stack_model.is_window_denotation`): stack-symbolic, positions ordered, entirely at/above the args base — the promotion's window stamp (`hike_promote.ml`) and the pointer-kind storage (`hike_types.storage_of` → `Ptr_window`) both read it | replace the body with `match positions_of_offsets ws with Some (lo, _) -> lo >= args_base …` (drop the `stack_offsets` requirement and the hi/ordering checks) | MOD-40f red: a plain in-band word at a window position classifies as window |
| MOD-43 | The one TP offset rule (`tls_tp_offset`): an affine analysis in the thread pointer — a bare constant is never a base; identity casts keep the form; width-changing casts of pointer-bearing values and non-unit coefficients are `Tp_nonlinear`; `(tp+1)-tp` cancels to absent. | In the cast arm, return `(c, v)` for every cast (no width check). | MOD-43.width-cast FAILs: the narrowing cast reads `Tp_based` instead of `Tp_nonlinear`. |
| MOD-44 | A runtime-sized descent from SP (`t := SP − {16,32}`) reads through `facts.denote` as the stack positions it stands for: `Stack` origin, not TOP. | Make `facts.denote` rebase the value onto an allocation frame. | MOD-44: the origin is not `Stack` or the value is TOP. |
| MOD-45 | An unbounded runtime SP decrement (`SP := SP − rcx` then a store above it) sets `runtime_residue`; masking the size to a byte keeps allocas. | In `layout_of_tree`, drop the `member_runtime` flag or flag every residue. | MOD-45: the unbounded layout is not runtime, or the bounded one is. |
| MOD-41 | term read sets use BAP terms and include the ABI transfer reads. | textually invert the pinned contract in `Hike_stack_model` | pin FAILs under that inversion (re-demonstrated by review) |
