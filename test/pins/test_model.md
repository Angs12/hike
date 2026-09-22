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
| MOD-07 | The loop-carried VLA is the event; the shape test is local to the def, so the widened loop head does not hide it. | In `event_rhs`, require a straight-line (single-predecessor) block. | MOD-07. |
| MOD-08 | `Hike_sections.layout_of_tree` carries the Region components (ascending ids) and no residue region for a precise tree. | In `src/hike_sections.ml` `layout_of_tree` (l.730), force the `Stack_residue` arm. | MOD-08; MOD-09 loses its regions. |
| MOD-09 | Region bytes are the occupied span aligned once, never span×access-width. | In `layout_of_tree`'s byte computation, multiply the aligned span by the access width. | MOD-09. |
| MOD-10 | A plain-TOP identity member forces the residue region (id 0) with the 64K unbounded floors. | In `layout_of_tree`, drop the `Stack_residue` floor (`stack_max`). | MOD-10; MOD-11. |
| MOD-11 | A plain-TOP-only residue sub takes the same unbounded floor. | As MOD-10. | MOD-11. |
| MOD-12 | `Hike_promote.rewrite_def` (`Conv_region`) rebinds a whole-access store's lhs and mem node to the region mem, keeping the SP address arithmetic. | In `src/hike_promote.ml`, `rewrite_def` (l.225): return the def unchanged. | MOD-12; also MOD-13..20. |
| MOD-13 | The nested load inside a BinOp def reads the region mem too (the -O0 cmp pattern). | In `rewrite_load_node`/`repoint_mapper` (l.182/213), skip loads nested below the rhs root. | MOD-13. |
| MOD-14 | `slot_read` (l.201) turns the full-cell args read (width 64) into the bare `hike_slot0` var. | In `slot_read`, return the load unchanged for the full-cell case. | MOD-14; also MOD-15/16. |
| MOD-15 | The aligned narrow args read (width 32 at cell start) splices a `LOW` cast. | In `slot_read`, drop the aligned-narrow arm. | MOD-15. |
| MOD-16 | The intra-cell args read (width 32 at byte 4) selects bits `[8d, 8d+bits)`. | In `slot_read`, drop the intra-cell `Extract` arm. | MOD-16. |
| MOD-17 | Write-closed Window: an Args cell that also contains a store takes Window storage on both sides (the read keeps its mem node and tag, never a slot). | In `conversion_of` (l.116), treat a stored Args cell as an `Arg_slot`. | MOD-17. |
| MOD-18 | `Hike_split_mem.normalize` splits the RMW; write-closure demotes the slot for both sides, so every memory node is on `window_mem`. | In `src/hike_split_mem.ml`, skip the split; or convert the hoisted read to a slot in the rewrite. | MOD-18. |
| MOD-19 | `Hike_jump.compile_sub` compiles flag idioms to value comparisons — no memory node rides a cond. | In `src/hike_jump.ml`, `compile_sub` returns the sub unchanged. | MOD-19. |
| MOD-20 | The load def converts to the region mem and the guard reads its converted temp transitively. | As MOD-12. | MOD-20. |
| MOD-21 | The emitter's VLA lane emits a real runtime-sized `%vla = alloca i8, i64`. | In `src/bil2llvm*.ml`, drop the VLA alloca emission. | MOD-21. |
| MOD-22 | The model SP binds to the alloca's integer (`%vla_i64 = ptrtoint`). | In the VLA emission, skip the SP bind. | MOD-22. |
| MOD-23 | Residue storage anchors through the entry SP Slot (`%sp_slot`; `%stack_0 = load`). | In the anchor emission, skip the `sp_slot` for the residue class. | MOD-23. |
| MOD-24 | Region storage anchors the SP Slot at region-0 + 8 (the SysV residue). | In the anchor emission, use a different anchor offset. | MOD-24. |
| MOD-25 | A storage-free sub emits no SP Slot and no region. | In the emitter, emit the `sp_slot` unconditionally. | MOD-25. |
| MOD-26 | An over-bound region request names itself on the channel (`hike: frame:` … `clamped`) and clamps. | In the frame clamp, emit silently (drop the `Hike_diag.warn`). | MOD-26. |
| MOD-27 | `Hike_stack_model.string_text_word`: a printable run crossing the word start covers the word. | In `src/hike_stack_model.ml` (l.356), return `false` unconditionally. | MOD-27. |
| MOD-28 | A NUL directly before the word means no crossing. | In `string_text_word`, drop the NUL check. | MOD-28. |
| MOD-29 | Pointer bytes before the word mean no crossing. | In `string_text_word`, drop the pointer-byte check. | MOD-29. |
| MOD-30 | A non-printable start byte never covers. | In `string_text_word`, treat a non-printable start byte as printable. | MOD-30. |
| MOD-31 | The first word of the image never crosses. | In `string_text_word`, drop the first-word guard. | MOD-31. |
| MOD-32 | Running off the front crosses iff the prefix is all printable. | In `string_text_word`, drop the all-printable-prefix scan. | MOD-32. |
| MOD-33 | `Hike_abi.is_sp` / `sp`: the stack pointer is RSP, and only RSP (SP-only, ADR 0008). | In `src/hike_abi.ml`, set the SysV `sp` to RBP (or make `is_sp` true for RBP). | MOD-33. |
| MOD-34 | RBP is an ordinary callee-saved GPR; no frame-pointer fact exists. | In `hike_abi.ml`, remove RBP from `callee_saved` (or `is_callee_saved`). | MOD-34. |
| MOD-35 | The SysV lanes: 6 integer args, 8 vector args, RAX/RDX returns; the unknown target totals 14 param lanes. | In `hike_abi.ml`, alter `int_param_regs`/`vector_param_regs`/`return_regs`. | MOD-35. |
| MOD-36 | The structural predicates partition the lanes (`is_return_reg`, `is_vector_param_reg`). | In `hike_abi.ml`, make `is_return_reg` true for RCX. | MOD-36. |
| MOD-37 | An unknown target falls back to the SysV record (`of_target` total; `addr_size_bits unknown = 0`). | In `hike_abi.ml`, make `of_target` raise on unknown, or return a nonzero `addr_size_bits`. | MOD-37. |
| MOD-38 | The `x86_64-gnu-elf` target reifies RSP as the SP. | In `hike_abi.ml`, make `of_target` skip the target SP reification. | MOD-38. |
| MOD-39 | The word size comes from the Target API: SysV carries 8; `of_target` derives `bits/8`. | In `hike_abi.ml`, hardcode the `word` field to a wrong value. | MOD-39. |
