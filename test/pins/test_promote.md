# Pins — test_promote

Module: `test/unit/test_promote.ml` (group `promote`, ids `PR-01`…`PR-22`),
merging every entry point of `test_cbat/test_promote.ml` in source order:
`run_promotion` (9 `T4-*` checks), `run_t10_rewrite` (5 `T10-*` checks),
`run_producer_promotion` (6 `PR-A*` checks), and `run_window_escape`
(2 `PR-WC*` checks).  Every source `check` site is carried as one pin; none
is retired.  The swallowing `try … with _ -> ()` that wrote
`/tmp/t10_prom_ir.txt` and the stale "promote_sub 3b recipe died" comment
were neither pins nor assertions and are dropped.

Production mechanisms: `src/hike_promote.ml` (`promote_sub`,
`rewrite_program`, `site_bindings_of_sub`, `call_resolution`), `src/hike_sections.ml`
(`attribute` / `stamp_tags` / `storage_of_range`), `src/hike_cfg_complete.ml`
(`retaddr_defs`), `src/hike_stack_model.ml` (`arg_slot`, `is_call_arg`), and
the emitter's promotion rendering `src/bil2llvm.ml` +
`src/bil2llvm_calls.ml` (promoted signature, `_hike_thunk`, `indirect_call`).

There is no `Test_seam` for this pass, so no fail-before switch can be
flipped from the test tier.  Production `src/` is never modified.  The
disable recipes below are textual and name the source site to break; the
recorded red is the state that recipe produces (re-demonstrated whenever the
cited mechanism changes).  Every pin builds its own fixture inside its
closure — no cross-pin state.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| PR-01 | `promote_sub` seeds the promoted parameter list from `facts.prom_arity` (`hike_slot0`/`hike_slot1`), and `bil2llvm` appends those promoted args after the ABI register lanes in the emitted body signature. | In `src/hike_promote.ml` `promote_sub`, drop the promoted-arg seeding: `Base.List.init facts.prom_arity …` → `[]`. | PR-01: the body signature lacks `i64 %hike_slot0, i64 %hike_slot1`, so `check_ir` misses the substring (review). |
| PR-02 | A site whose `prom_resolved` maps its jmp tid to `Some callee_tid` is rewritten to a direct call through the promoted signature; the slots the caller did not pass stay `undef`. | In `src/hike_promote.ml`, ignore the resolved map: `rewrite_program` takes the unresolved (pointer) arm for every site. | PR-02: the resolved site emits the pointer call, so `call void @"<callee>"(` is absent (review). |
| PR-03 | `bil2llvm_calls.ml` emits a `_hike_thunk` twin with `internal` linkage for each promoted body. | In `src/bil2llvm_calls.ml`, emit the thunk with external linkage (drop `internal`). | PR-03: `define internal void @"<callee>_hike_thunk"` no longer matches (review). |
| PR-04 | The thunk's synthetic indirect convention is the ABI register lanes plus `ptr %hike_window` — the window base, never SP. | In `src/bil2llvm_calls.ml`, replace the trailing `hike_window` parameter with the SP register in the thunk signature. | PR-04: the `… ptr %hike_window)` tail is absent from the thunk signature (review). |
| PR-05 | The thunk unpacks the window slots by calling the promoted body with the register lanes. | In `src/bil2llvm_calls.ml`, make the thunk emit an empty body (no call to the promoted body). | PR-05: `call void @"<callee>"(i64 %RDI, i64 %RSI, i64 %` is absent (review). |
| PR-06 | The thunk reads the window slots through the window pointer (`getelementptr i8, ptr %hike_window`). | In `src/bil2llvm_calls.ml`, substitute the slots with `undef` instead of loading them. | PR-06: no `getelementptr i8, ptr %hike_window` appears (review). |
| PR-07 | An unresolvable site (`prom_resolved = None`) takes the pointer call through the synthetic `@indirect_call` signature. | In `src/hike_promote.ml` `rewrite_program`, resolve every site (treat `None` as a direct call). | PR-07: the `call { i64, i64 } %` pointer call is absent (review). |
| PR-08 | The unresolved site's pointer call never lands on the promoted body directly by name. | Same recipe as PR-07; additionally force the fallback target name to the callee. | PR-08: `call { i64, i64 } @prom_callee(` appears (review). |
| PR-09 | `bil2llvm.ml` emits the synthetic `@indirect_call` signature: six GP lanes, eight YMM lanes, and the trailing `ptr %hike_window`. | In `src/bil2llvm.ml`, drop the trailing window parameter from the `indirect_call` declaration. | PR-09: the `@indirect_call(…, ptr)` full signature substring is absent (review). |
| PR-10 | `promote_sub` adds one real BIR `arg` per promoted slot, named `hike_slotN` (`Hike_stack_model.arg_slot`). | In `src/hike_promote.ml` `promote_sub`, drop the `Arg.create` install. | PR-10: `Term.enum arg_t sub'` contains no `Cu.arg_slot ~word:8 0` (review). |
| PR-11 | The arg-term rewrite preserves the sub's tid (`Sub.Builder` over the original tid). | In `src/hike_promote.ml` `promote_sub`, mint a fresh tid for the rebuilt sub. | PR-11: `Tid.equal (Term.tid sub') (Term.tid sub)` fails (review). |
| PR-12 | `Hike_sections.stamp_tags` keeps the `sec_tag` on an identity stack access through the stamp. | In `src/hike_sections.ml` `stamp_tags`, skip defs whose rhs is an unclassified identity access. | PR-12: `Sm.sec_tag keep_def` is `None` (review). |
| PR-13 | `rewrite_program`'s site rewrite binds the call-arg def (`Hike_stack_model.is_call_arg`) immediately after the storing def. | In `src/hike_promote.ml`, insert the call-arg def at the block head instead of `Term.next def_t`. | PR-13: the call-arg def's index is not `i_store + 1` (review). |
| PR-14 | The bound call-arg def carries the storing def's written bytes (`Model.store_data_of_rhs`). | In `src/hike_promote.ml`, bind the call-arg def to `Bil.Var (Def.lhs b.sb_def)` (the memory node) instead of the store data. | PR-14: `Def.rhs arg_def` is not the literal `7` (review). |
| PR-15 | `Hike_sections.attribute` classifies a `[entry RSP+8]` read as `Arg_slot 0` when the sub's arity is 1 and no window is present. | In `src/hike_sections.ml`, force the incoming-slot classification to `Stack_residue`. | PR-15: the tree's `Arg_slot` list is not `[0]` (review). |
| PR-16 | `Hike_cfg_complete.retaddr_defs` puts the `[RSP+0]` load in the return-address set (it never forces a window parameter). | In `src/hike_cfg_complete.ml` `retaddr_defs`, stop filtering loads at the entry-RSP cell `{0}`. | PR-16: `Core.Set.mem a2_retaddr (Term.tid a2_ld)` is false (review). |
| PR-17 | A store into the caller window writes real memory: the touched slot is write-closed into `Stack_residue` (Window), so its reads take the window. | In `src/hike_sections.ml`, treat written args slots as unbound `Arg_slot` (skip the write-closed demotion). | PR-17: `storage_of_range` at `[+8,+15]` is not `Some Stack_residue` (review). |
| PR-18 | The demotion is exact: an 8-byte store at `[entry RSP+8]` touches slot 0's cell only; slot 1 stays `Arg_slot 1`. | In `src/hike_sections.ml`, widen the written range by one slot on either side. | PR-18: `storage_of_range` at `[+16,+23]` is no longer `Some (Arg_slot 1)` (review). |
| PR-19 | `Hike_promote.site_bindings_of_sub` maps a site's outgoing stores to SysV slots by the store's own start address; a same-slot re-store is last-wins. | In `src/hike_promote.ml` `site_bindings_of_sub`, take the first store per slot instead of the last. | PR-19: the single binding's `sb_def` is `a6_st1`, not `a6_st2` (review). |
| PR-20 | `Hike_promote.call_resolution` records no resolution for an indirect target with `symtab = None` (the target denotation is symbolic/unbounded). | In `src/hike_promote.ml` `call_resolution`, fabricate a direct resolution when the target is symbolic. | PR-20: `Core.Map.find resolved (Term.tid j)` is `Some (Some _)` instead of `Some None` (review). |
| PR-21 | The va_start triangle's middle sub (six GP args, no incoming stack-arg read) keeps every slot unbound (arity 0) and serves the SP-derived pointer from the window (`Stack_residue`). | In `src/hike_sections.ml`, classify the mid sub's `Sm.Args` members as `Arg_slot` regardless of the absent incoming read. | PR-21: an `Arg_slot` appears in the tree, so the `for_all` unbound check fails (review). |
| PR-22 | A pointer SP-derived at the storing block's entry is visible to the escape evaluation (the boundary-visible twin), so the anchor's cell is Window-served. | In `src/hike_sections.ml`, evaluate escapes only at a def's own pre-state and drop the block-entry fallback. | PR-22: the twin's tree carries no `Stack_residue` member (review). |
