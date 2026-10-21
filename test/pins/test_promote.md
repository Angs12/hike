# Pins — test_promote

Module: `test/unit/test_promote.ml` (group `promote`, ids `PR-01`…`PR-43`),
merging every entry point of `test_cbat/test_promote.ml` in source order:
`run_promotion` (9 `T4-*` checks), `run_t10_rewrite` (5 `T10-*` checks),
`run_producer_promotion` (6 `PR-A*` checks), and `run_window_escape`
(2 `PR-WC*` checks).  Every source `check` site is carried as one pin; none
is retired.  The swallowing `try … with _ -> ()` that wrote
`/tmp/t10_prom_ir.txt` and the stale "promote_sub 3b recipe died" comment
were neither pins nor assertions and are dropped.

Production mechanisms: `src/hike_promote.ml` (`promote_sub`,
`rewrite_program`, `call_resolution`), `src/hike_sections.ml`
(`attribute` / `stamp_tags` / `storage_of_range`), `src/hike_cfg_complete.ml`
(`retaddr_defs`), `src/hike_core/hike_stack_model.ml` (`arg_slot`,
`is_call_arg`), and the emitter's promotion rendering
`src/hike_emit/bil2llvm.ml` + `src/hike_emit/bil2llvm_calls.ml` (promoted
signature, `_hike_thunk`, `indirect_call`).

There is no `Test_seam` for this pass, so no switch can be
flipped from the test tier.  Production `src/` is never modified.  The
disable recipes below are textual and name the source site to break; the
recorded red is the state that recipe produces (re-demonstrated whenever the
cited mechanism changes).  Every pin builds its own fixture inside its
closure — no cross-pin state.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| PR-04 | The thunk's synthetic indirect convention is the ABI register lanes plus `ptr %hike_window` — the window base, never SP. | In `src/hike_emit/bil2llvm_calls.ml`, replace the trailing `hike_window` parameter with the SP register in the thunk signature. | PR-04: the `… ptr %hike_window)` tail is absent from the thunk signature (review). |
| PR-08 | The unresolved site's pointer call never lands on the promoted body directly by name. | Same recipe as PR-07; additionally force the fallback target name to the callee. | PR-08: `call { i64, i64 } @prom_callee(` appears (review). |
| PR-09 | `bil2llvm.ml` emits the synthetic `@indirect_call` signature: six GP lanes, eight YMM lanes, and the trailing `ptr %hike_window`. | In `src/hike_emit/bil2llvm.ml`, drop the trailing window parameter from the `indirect_call` declaration. | PR-09: the `@indirect_call(…, ptr)` full signature substring is absent (review). |
| PR-12 | `Hike_sections.stamp_tags` keeps the `sec_tag` on an identity stack access through the stamp. | In `src/hike_sections.ml` `stamp_tags`, skip defs whose rhs is an unclassified identity access. | PR-12: `Sm.sec_tag keep_def` is `None` (review). |
| PR-16 | `Hike_cfg_complete.retaddr_defs` puts the `[RSP+0]` load in the return-address set (it never forces a window parameter). | In `src/hike_cfg_complete.ml` `retaddr_defs`, stop filtering loads at the entry-RSP cell `{0}`. | PR-16: `Core.Set.mem a2_retaddr (Term.tid a2_ld)` is false (review). |
| PR-17 | A store into the caller window writes real memory: the touched slot is write-closed into `Stack_residue` (Window), so its reads take the window. | In `src/hike_sections.ml`, treat written args slots as unbound `Arg_slot` (skip the write-closed demotion). | PR-17: `storage_of_range` at `[+8,+15]` is not `Some Stack_residue` (review). |
| PR-18 | The demotion is exact: an 8-byte store at `[entry RSP+8]` touches slot 0's cell only; slot 1 stays `Arg_slot 1`. | In `src/hike_sections.ml`, widen the written range by one slot on either side. | PR-18: `storage_of_range` at `[+16,+23]` is no longer `Some (Arg_slot 1)` (review). |
| PR-19 | `Hike_promote.site_bindings_of_sub` maps a site's outgoing stores to SysV slots by the store's own start address; a same-slot re-store is last-wins. | In `src/hike_promote.ml` `site_bindings_of_sub`, take the first store per slot instead of the last. | PR-19: the single binding's `sb_def` is `a6_st1`, not `a6_st2` (review). |
| PR-20 | `Hike_promote.call_resolution` records no resolution for an indirect target with `symtab = None` (the target denotation is symbolic/unbounded). | In `src/hike_promote.ml` `call_resolution`, fabricate a direct resolution when the target is symbolic. | PR-20: `Core.Map.find resolved (Term.tid j)` is `Some (Some _)` instead of `Some None` (review). |
| PR-21 | A pure SP-derived value above entry with no Args-space memory access binds no Args cell and does not require an incoming window parameter. | In `src/hike_sections.ml`, derive `window_param` from the SP-value stamp rather than actual Args-space members. | PR-21: the layout has `window_param = true` (review). |
| PR-22 | The SP-derived value remains stamped, but the entry-SP expression does not force a `hike_window` parameter. | In `src/hike_promote.ml`, require a window parameter for every stamped window value. | PR-22: the rewritten sub gains an unnecessary window parameter (review). |
| PR-23 | The one address map: a region address def's value is its storage's base (`stack_r2_ptr`, displacement folded to zero) and the local access's address names its own region (`stack_r1_ptr`) — `def_facts`/`offset_of` in `src/hike_promote.ml`. | In `src/hike_promote.ml` `def_facts`, drop the value-path `region_base` rewrite (return `no_fact`). | PR-23: RBP's rhs is `Var RSP`, and the 42-store's address is `RBP - 16` — no `stack_rN_ptr` (review). |
| PR-25 | A reloaded-base access routes to its proven storage: the escaped cell write-closes into the residue and the through-pointer store's address is `stack_r0_ptr + displacement` over the reloaded pointer's singleton offset. | In `src/hike_promote.ml` `def_facts`, gate the access address rewrite on `id <> Model.residue_id`. | PR-25: the through-pointer store keeps `Var rw_p` as its address — the raw lane (review). |
| PR-27 | A window access's address is rewritten to `hike_window + off` (the window's coordinate IS the entry-relative offset) — `def_facts`' Conv_window arm in `src/hike_promote.ml`. | In `src/hike_promote.ml` `def_facts`, drop the Conv_window address rewrite (return `fact`). | PR-27: the crossing read's address stays `RBP + 20` (review). |
| PR-28 | A window value def (at/above the args base, the signature carrying the window parameter) takes the window parameter as its base. | In `src/hike_promote.ml` `def_facts`, drop the window value arm's `window_param` guard's rewrite. | PR-28: `rw_w` keeps `RBP + 20` (review). |
| PR-30 | A constant address def's value routes to its component's base (`sec_comp_<id>_ptr + (const − comp_lo)`, folded at the low bound) — the plain arm of `def_facts` in `src/hike_promote.ml`, keyed on the binding wholly owning the constant (copy-relocated slots keep the raw lane). | In `src/hike_promote.ml` `def_facts`, drop the plain arm's rewrite (return `acc`). | PR-30: `rw_c` keeps `0x1000` (review). |
| PR-26 | a residue-routed access's value is `residue_ptr + (disp − rel)` — the residue takes the one address rule | re-derive the address geometrically at emission | pin FAILs: the base is not the residue's |
| PR-37 | The lifted va_list construction — the incoming parameter registers stored into the sub's own frame beside an at/above-entry overflow pointer stored into the frame — stamps the sub variadic (`is_construction` and the `stamp` pass in `src/hike_core/hike_variadic.ml`), so the emitter declares a real LLVM variadic definition. | In `src/hike_core/hike_variadic.ml` `is_construction`, drop the overflow-pointer half (keep only the register spills). | PR-37: `Hike.Variadic.is_variadic sub'` is false and the `, ...)` tail is absent (review). |
| PR-38 | The register spills alone, with no overflow pointer, are not the va_list construction. | In `src/hike_core/hike_variadic.ml` `is_construction`, drop the register-spill half (keep only the overflow pointer). | PR-38: `Hike.Variadic.is_variadic sub'` is true (review). |
| PR-39 | A runtime index in an ABI lane (a bounded non-stack denotation) folds into the access's region: the per-use leaf kind is the value fact, never the register's ABI role. | In `src/hike_promote.ml`, exclude the ABI parameter/return lanes from `offset_of`'s runtime pieces. | PR-39: the indexed store's address keeps `Var RBP` (the raw lane) instead of a `stack_r1_ptr` base (review). |
| PR-31 | the per-word-cell split: a two-cell Args binding promotes each cell to its own slot. | textually invert the pinned contract in `Hike_sections` | pin FAILs under that inversion (re-demonstrated by review) |
| PR-32 | a promoted access keeps its memory node, addressed at the slot pointer. | textually invert the pinned contract in `Hike_sections` | pin FAILs under that inversion (re-demonstrated by review) |
| PR-33 | the promoted slot parameter is a pointer (Mem-typed). | textually invert the pinned contract in `Hike_sections` | pin FAILs under that inversion (re-demonstrated by review) |
| PR-34 | the caller binds the slot address (the store's own address). | textually invert the pinned contract in `Hike_sections` | pin FAILs under that inversion (re-demonstrated by review) |
| PR-35 | the emitted slot parameter is an LLVM pointer and the access loads through it. | textually invert the pinned contract in `Hike_sections` | pin FAILs under that inversion (re-demonstrated by review) |
| PR-36 | the twin forwards the window slot pointer (no load). | textually invert the pinned contract in `Hike_sections` | pin FAILs under that inversion (re-demonstrated by review) |
| PR-40 | Retargeting an SSA indirect call to an ordinary sub rewrites the call target, leaves the SSA marker unchanged, and keeps the surviving written/read lane identities. | Re-create the call's effects from names instead of retaining the previous lane versions. | PR-40 surviving result/argument identities FAIL: lanes are rebuilt with new identities. |
| PR-41 | Retargeting an SSA call to a lane-free target drops the call's write lanes and rets. | Keep the previous lane set when the new target has none. | PR-41 FAILs: writes remain non-empty. |
| PR-42 | Promotion keeps an SSA sub SSA and gives its promoted slot parameters entry version 0. | Assign fresh versions to promoted parameters. | PR-42 FAILs: a slot's index is not 0. |
| PR-43 | The storage rewrite of an SSA sub with stack, window, and global accesses leaves every var with a single definition and every read defined. | Emit each storage access as a fresh def of the underlying var. | PR-43 single definitions or reads defined FAILs. |
