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
| RES-06 | the completion's canonical return rewrite — a retaddr-read return-less indirect call lands as a var-free return-less call (`hike_cfg_complete.ml:501-505, 624`) | at `:624` emit the untouched call jmp instead of `ret_jmp ~word_bits` | RES-06 red: `jmps_of_blk j1' 0` no longer matches `(None, Indirect (Unknown _))` |
| RES-07 | the retaddr predicate is scoped to return-less calls — a `return=Some` call with the same target stays a call (`:623-624`) | drop the `Call.return c = None` guard so the ret arm fires for any return | RES-07 red: the control call is rewritten |
| RES-08 | `resolve_phase` materialization — a complete bounded dispatch becomes one delta-guarded goto per case target (`hike_cfg_complete.ml:409-500`) | make `bounded_words` answer `None` for the two-word set (raise the `~cap` at `:94` to 1) | RES-08 red: block 3 keeps the single indirect goto |
| RES-09 | the bake rule — a one-word resolution materializes nothing (`bounded_words` requires a bounded plain set; the dispatch stays) | make `bounded_words` accept card 1 (drop the `enumerate` completeness gate, `:94-101`) | RES-09 red: the single indirect goto is rewritten |
| RES-10 | the fused solve's warm closure — the selector widens in the same run that first resolved the dispatch (`resolve_phase` + `Hike.Vsa.fixpoint`) | resolve on a cold solve (drop the warm re-seed in `Hike_vsa.fixpoint`) | RES-10 red: `sel_card ≠ 2` |
| RES-11 | `split_entry` — a mid-block case entry splits its container; the fresh block takes the address (`hike_cfg_complete.ml:164-322`) | disable the split at `:314` (keep `sub` and the container tid) | RES-11 red: no `0x3010` entry in `block_addrs` / no address tag |
| RES-12 | the exit series — one guarded goto per table entry (`hike_cfg_complete.ml:409-500`) | same `bounded_words` `~cap` recipe as RES-08 | RES-12 red: block 1 has no two-goto series |
| RES-13 | the indirect-resolvable liveness rule — a fresh split the materialization didn't claim stays because the surviving indirect transfer still denotes its address (`indirect_live` + `prune_unreachable`, `hike_cfg_complete.ml:646-746`) | make `indirect_live` answer `Tid.Set.empty` for every transfer | RES-13 red: the address-bearing `0x3008` block is pruned |
| RES-14 | the loud failure — a resolvable dispatch word the map cannot name and no re-lift can materialize raises (`split_entry`, `hike_cfg_complete.ml:195-203`) | return `(sub, container_tid)` instead of `failwith` at `:199` | RES-14 red: `produce` no longer raises `Failure` |
| RES-15 | a foreign pointer target is not a dispatch — the indirect transfer stays (`rewritten_jmps` `:605`, `resolved_pairs_of`) | admit the foreign constant as a case word (map it in `block_addrs`) | RES-15 red: the `Indirect` goto is rewritten |
| RES-16 | a TOP target is not a dispatch — the indirect transfer stays (`rewritten_jmps` `:605`) | treat the TOP denotation as a bounded case word (drop the `is_top` guard, `:84`) | RES-16 red: the `Indirect` goto is rewritten |
| RES-17 | `Mem.Key.of_wordset` keys the entry-RSP cell (`Ws.stack_word_i64 0`) — the RET-ND1 fixture's precondition | make `Cbat_clp_set_composite.stack_word_i64` answer a set `of_wordset` rejects (e.g. `top 64`) | RES-17 red: `check_bound` sees `None` |
| RES-18 | `retaddr_defs` with a seeded bounded `{0}` entry-RSP cell — the load is the retaddr read (`hike_cfg_complete.ml:32-46`) | same `is_return_address` guard recipe as RES-05 | RES-18 red: the seeded load is not in the retaddr set |
| RES-19 | the resolution phase skips retaddr-read targets — a bounded retaddr target grows no edge and splits nothing (`hike_cfg_complete.ml:48-53, 314`) | drop the `retaddr_read` filter in `prepare_dispatches` (`:314-328`) | RES-19 red: `events5`, `fresh5'`, or `resolved5'` non-empty |
| RES-20 | the retaddr skip leaves the epilogue sub's blocks and call untouched (`resolve_phase`, `hike_cfg_complete.ml:784`) | same `retaddr_read` filter removal as RES-19 | RES-20 red: blocks or the call differ from the input |
| RES-21 | the materializer — a dispatch word in no block re-lifts its case body and retargets a direct target naming an existing block (`materialize_block`, `hike_cfg_complete.ml:105-162`) | make the pin's `lift_at` answer `None` (the pre-materializer behavior) | RES-21 red: `produce` raises `Failure` (no block named) |
