# Pins — test_resolve (module `resolve`, prefix `RES`)

One row per pin. Completeness: the id column equals
`dune exec test/unit/test_resolve.exe -- list`.
Production `src/` is never touched; recipes are the textual change that
disables the mechanism, re-demonstrated by review when it changes.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| RES-01 | `Hike.Resolve.resolve_target` — a singleton whose word names a lifted sub returns `Some tid` (`src/hike_resolve.ml:12-15`, via `Model.singleton_i64` + `lookup`) | replace `\| Some v -> lookup v` with `\| Some _ -> None` | RES-01 red: `None ≠ Some res_callee` |
| RES-02 | `resolve_target` — a bounded multi-word set is not a singleton, so it takes the pointer call (`None`) | replace `\| None -> None` with `\| None -> Some (Tid.for_name "res_callee")` | RES-02 red: the two-word set resolves |
| RES-03 | `resolve_target` — the `lookup` decides foreignness; a foreign singleton's word names no lifted sub | at the `Some v` arm call `fun _ -> Some (Tid.for_name "res_callee")` instead of `lookup` | RES-03 red: the foreign singleton resolves |
| RES-04 | `resolve_target` — an unresolvable (TOP/infinite) set never reaches `lookup` | same `\| None -> Some (Tid.for_name "res_callee")` recipe as RES-02 | RES-04 red: the TOP set resolves |
| RES-05 | `Hike.Cfg_complete.retaddr_defs` — a load's ADDRESS denotation meets `Model.is_return_address` (the entry-RSP cell) (`hike_cfg_complete.ml:32-46`) | change the guard at `hike_cfg_complete.ml:43` to `Ok _ when false` | RES-05 red: the epilogue's `[RSP]` load is not in the retaddr set |
| RES-06 | the completion's canonical return rewrite — a retaddr-read return-less indirect call lands as the direct `hike_return` edge (`hike_cfg_complete.ml:32-53, 615-645`) | at the return arm emit the untouched call jmp instead of `ret_jmp` | RES-06 red: `Hike_return.is_jmp` is false |
| RES-07 | the retaddr predicate is scoped to return-less calls — a `return=Some` call with the same target stays a call (`:623-624`) | drop the `Call.return c = None` guard so the ret arm fires for any return | RES-07 red: the control call is rewritten |
| RES-08 | the split-blocks materializer — a COMPLETE bounded dispatch (every word names an in-sub block) renders one guarded goto per case target, guards in the TARGET domain (`texp = word`; a module-address base summand is subtracted), the last (exhaustive) arm unconditional (`Hike_split_blocks.series` + `resolved_cases`) | make `bounded_words` answer `None` (the empty-map arm) | RES-08 red: block 3 keeps the single indirect goto |
| RES-09 | the bake rule — a one-word resolution materializes nothing (`bounded_words` requires a bounded plain set; the dispatch stays) | make `bounded_words` accept card 1 (drop the `enumerate` completeness gate) | RES-09 red: the single indirect goto is rewritten |
| RES-10 | the fused solve's warm closure — the selector widens in the same run that first resolved the dispatch (`resolve_phase` + `Hike.Vsa.fixpoint`) | resolve on a cold solve (drop the warm re-seed in `Hike_vsa.fixpoint`) | RES-10 red: `sel_card ≠ 2` |
| RES-13 | the completeness gate — a word set with a word naming no in-sub block renders NOTHING (a partial series would drop live cases); the indirect transfer stays as it came and the word rides the fact channels to the driver's decode (`resolved_pairs_of`'s `length pairs = length ws`) | drop the completeness gate (accept partial pairs) | RES-13 red: a two-case partial series replaces the transfer |
| RES-14 | the decline — a dispatch word the map cannot name is a fact-channel decline, never a failure (`resolved_pairs_of`'s `else None` arm) | `failwith` at the incomplete-pairs arm instead of `None` | RES-14 red: `produce` raises |
| RES-27 | RETADDR-ONCE: the completion's shared return-address set serves both consumers — the return-less indirect call becomes the canonical return edge and the dispatch keeps its two cases; the resolved map covers both cells and materialization keeps the return and dispatch. | Recompute the retaddr set per consumer, or drop the second cell from `retaddr_defs`. | RES-27a/b/c FAIL: a return-address cell is missed, the dispatch loses a case, or materialization drops the return edge. |

RES-11 and RES-12 are DELETED (the drive-loop reimplementation): the
mid-block case-entry split (`split_entry`) is gone — the completion
creates nothing; a mid-block word rides the fact channels to the
driver's decode, which materializes the block in the owning sub.  The
coverage is the drive probe and the stripped corpus (jump_table_sw),
not a unit pin.
| RES-15 | a foreign pointer target is not a dispatch — the indirect transfer stays (`Hike_split_blocks.series` declines on `slot_of_target`; `resolved_pairs_of`) | admit the foreign constant as a case word (map it in `block_addrs`) | RES-15 red: the `Indirect` goto is rewritten |
| RES-19 | the resolution phase skips retaddr-read targets — a bounded retaddr target grows no edge (`dispatch_target`'s `retaddr_read` filter, `hike_cfg_complete.ml`) | drop the `retaddr_read` filter in `dispatch_target` | RES-19 red: `events5` or `resolved5'` non-empty |
| RES-22 | the lifted `ret` is a `Goto` (BAP lifts `retq` as `jmp #retaddr`); a retaddr-proven `Goto (Indirect (Var v))` canonicalizes to the direct `hike_return` edge (`ret_rewrite`, `hike_cfg_complete.ml`) | drop the `retaddr_read` guard so the `Goto` arm always takes the dispatch series | RES-22 red: the jmp stays `Goto (Indirect (Var ...))` (emitted as an `indirectbr`) |
| RES-23 | The completion owns the edge set (`hike_cfg_complete.ml` `materialize_fallthroughs`): a conditional goto's implicit false edge becomes an explicit `Goto`, and a destination two jumps share collapses to ONE unconditional edge. | Drop the dedupe (keep every jump) or skip the materialization. | (a) `[when C goto B1; goto B1]` stays two edges; (b) the lone guarded goto keeps no named false edge. |
| RES-25 | a relative-offset table's bounded denotation materializes the case arms in `Hike.Split_blocks.materialize` (the last exhaustive arm is unconditional) | make `bounded_words` answer `None` | RES-25 red: the dispatch keeps its indirect goto |
| RES-26 | a dispatch whose target adds table data to a `Rip`-denoted base summand guards `target - summand = word - base`, so the base's relocation cancels; the base register's earlier-ordered, non-reaching redefinition is irrelevant (`Hike_cfg_complete.module_base`) | make `module_base` report no base | RES-26b red: the guards compare runtime targets against module addresses |
