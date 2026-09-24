# DCE pins

Module `Hike_dce` (`src/hike_dce.ml`), driven by
`test/unit/test_dce.ml` (ids `DCE-01`…).  Mechanism: the never-used
sweep to a fixpoint — its load roots are the vars the promote rewrite
created, its escape roots the storages with identity members.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| DCE-01 | `Hike.Dce.dce` is total on `Theory.Target.unknown`; a jmp-read def chain survives, an unused def dies | drop the jmp-read root from the liveness roots in `src/hike_dce.ml` | all but one def survives → `List.length defs = 2` fails |
| DCE-02 | the canonical direct return edge stands; the popped-address def dies; indirect-with-return and direct calls stay untouched | re-introduce the `mem[RSP]` load in the epilogue rewrite | the popped-address def survives → `t_gone` fails |
| DCE-03 | ABI return/param regs, memory writes and intrinsic interface vars always survive unread | remove `RAX`/`RDI`/memory/intrinsic from the always-keep set | `lhs_set` loses a member → the length/mem checks fail |
| DCE-04 | the two-tier region-mem rule: a fissioned store chain dies iff no Load roots it | make `region_mem` stores always live | `dead_count = 0` fails |
| DCE-05 | the sp/`frame_anchor` lane survives iff used; the unused sp-value def dies on both paths | keep every SP-derived def unconditionally | the `pn`/`cn` name lists change → fails |
| DCE-06 | a `Sub.intrinsic` sub passes through `dce` unchanged | run the sweep on intrinsic subs | the dead def is deleted → length 1 fails |
| DCE-07 | a never-loaded region-mem store chain survives when rooted as escape storage | drop `~roots` | the chain is swept → length 2 fails |
