# test_model pins

Module `test/unit/test_model.ml` (ids `MOD-01`..`MOD-39`), migrating
`test_cbat/test_model.ml`.  Every source `check`/`check_bound` site is carried
as one pin, in source order across the six entry points
(`run_producer_record`, `run_layout`, `run_stl_rewrite`, `run_emitter_shapes`,
`run_text`, `run_abi_and_kb`); none retired.  Mechanism: the producer record
(the composed fixpoint / VLA-event detection), the layout from the finalized
tree, stack-to-locals fission, the emitter's alloca shapes, the printable-run
rule, and the Abi/Kb convention facts.

The mechanisms are not Test_seam-switchable, so — per the lane spec
`§Fail-before` — the disable recipes below are textual (production `src/` is
never touched) and the red is re-demonstrated by review when the mechanism
changes.  Each recipe names the pins it turns red; no measured red is claimed
here.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| MOD-01 | `Hike_promote.dynamic_alloc_tids_of` reads the SP def's value: a literal decrement and a chain-resolved constant are not VLA events. | In `src/hike_promote.ml`, `event_rhs` (l.325): make the literal/chain arm an event. | MOD-01. |
| MOD-02 | The runtime-unbounded decrement (`SP := SP − TOP`) is the VLA event; the literal decrement is not. | In `event_rhs`, drop the unbounded-decrement arm (identity). | MOD-02; MOD-03/04/05/07 lose their event. |
| MOD-03 | `Hike_stack_model.stamp_dyn_allocs` writes the dyn-alloc fact onto the def's value; `def_is_dyn_alloc` reads it. | In `src/hike_stack_model.ml`, make `stamp_dyn_allocs sub = sub` (l.583), or `def_is_dyn_alloc _ = false` (l.559). | MOD-03. |
| MOD-04 | The VLA chain resolves through the sequential state, so a two-temp spelling still fires on the SP def. | In `event_rhs`, do not chase the `Var` alias chain. | MOD-04. |
| MOD-05 | The plus-form (a negative size ADDED) is the event — the value carries the unbounded stack position, not the MINUS spelling. | In `event_rhs`, remove the PLUS arm. | MOD-05. |
| MOD-06 | A provably-above PLUS adjustment (hull `[0..63]`) is not the event — the def's value direction decides. | In `event_rhs`, treat every SP-adjusting PLUS as an event. | MOD-06. |
| MOD-07 | A VLA in a looping sub is the event; the seed reads the final denotations, so the loop's widening does not hide it. | Make `vla_seed` require a straight-line (single-predecessor) block. | MOD-07. |
| MOD-10 | A plain-TOP identity member forces the residue region (id 0) with the 64K unbounded floors. | In `layout_of_tree`, drop the `Stack_residue` floor (`stack_max`). | MOD-10; MOD-11. |
| MOD-17 | Write-closed Window: an Args cell that also contains a store takes Window storage on both sides (the read keeps its mem node and tag, never a slot). | In `conversion_of` (l.116), treat a stored Args cell as an `Arg_slot`. | MOD-17. |
| MOD-18 | `Hike_split_mem.normalize` splits the RMW; write-closure demotes the slot for both sides, so every memory node is on `window_mem`. | In `src/hike_split_mem.ml`, skip the split; or convert the hoisted read to a slot in the rewrite. | MOD-18. |
| MOD-19 | `Hike_jump.compile_sub` compiles flag idioms to value comparisons — no memory node rides a cond. | In `src/hike_jump.ml`, `compile_sub` returns the sub unchanged. | MOD-19. |
| MOD-20 | The load def converts to the region mem and the guard reads its converted temp transitively. | As MOD-12. | MOD-20. |
| MOD-33 | `Hike_abi.is_sp` / `sp`: the stack pointer is RSP, and only RSP (SP-only, ADR 0008). | In `src/hike_abi.ml`, set the SysV `sp` to RBP (or make `is_sp` true for RBP). | MOD-33. |
| MOD-34 | RBP is an ordinary callee-saved GPR; no frame-pointer fact exists. | In `hike_abi.ml`, remove RBP from `callee_saved` (or `is_callee_saved`). | MOD-34. |
| MOD-37 | An unknown target falls back to the SysV record (`of_target` total; `addr_size_bits unknown = 0`). | In `hike_abi.ml`, make `of_target` raise on unknown, or return a nonzero `addr_size_bits`. | MOD-37. |
| MOD-38 | The `x86_64-gnu-elf` target reifies RSP as the SP. | In `hike_abi.ml`, make `of_target` skip the target SP reification. | MOD-38. |
| MOD-39 | The word size comes from the Target API: SysV carries 8; `of_target` derives `bits/8`. | In `hike_abi.ml`, hardcode the `word` field to a wrong value. | MOD-39. |
| MOD-40 | The ONE caller-window denotation (`Hike_stack_model.is_window_denotation`): stack-symbolic, positions ordered, entirely at/above the args base — the promotion's window stamp (`hike_promote.ml`) and the pointer-kind storage (`hike_types.storage_of` → `Ptr_window`) both read it | replace the body with `match positions_of_offsets ws with Some (lo, _) -> lo >= args_base …` (drop the `stack_offsets` requirement and the hi/ordering checks) | MOD-40f red: a plain in-band word at a window position classifies as window |
| MOD-43 | The one TP offset rule (`tls_tp_offset`): an affine analysis in the thread pointer — a bare constant is never a base; identity casts keep the form; width-changing casts of pointer-bearing values and non-unit coefficients are `Tp_nonlinear`; `(tp+1)-tp` cancels to absent. | In the cast arm, return `(c, v)` for every cast (no width check). | MOD-43.width-cast FAILs: the narrowing cast reads `Tp_based` instead of `Tp_nonlinear`. |
