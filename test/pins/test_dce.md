# DCE pins

Module `Hike_dce` (`src/hike_dce.ml`), driven by
`test/unit/test_dce.ml` (ids `DCE-01`…).  Mechanism: the never-used
sweep to a fixpoint over defs AND phis — its load roots are the vars the
promote rewrite created, its escape roots the storages with identity
members (carried on the facts record to the sweep's own pass, which runs
after `hike-types`, immediately before the emitter).

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| DCE-02 | the canonical direct return edge stands; the popped-address def dies; indirect-with-return and direct calls stay untouched | re-introduce the `mem[RSP]` load in the epilogue rewrite | the popped-address def survives → `t_gone` fails |
| DCE-03 | ABI return/param regs, memory writes and intrinsic interface vars always survive unread | remove `RAX`/`RDI`/memory/intrinsic from the always-keep set | `lhs_set` loses a member → the length/mem checks fail |
| DCE-04 | the two-tier region-mem rule: a fissioned store chain dies iff no Load roots it | make `region_mem` stores always live | `dead_count = 0` fails |
| DCE-05 | the sp/`frame_anchor` lane survives iff used; the unused sp-value def dies on both paths | keep every SP-derived def unconditionally | the `pn`/`cn` name lists change → fails |
| DCE-06 | a `Sub.intrinsic` sub passes through `dce` unchanged | run the sweep on intrinsic subs | the dead def is deleted → length 1 fails |
| DCE-07 | a never-loaded region-mem store chain survives when rooted as escape storage | drop `~roots` | the chain is swept → length 2 fails |
| DCE-08 | a phi whose result no survivor reads is swept, and the operand defs cascade with it (the phi arm) | count phi reads as permanent (feed `perm` from `blk_reads`) | the phi and the `d8_v` defs survive → `phi_gone`/`v_gone` fail |
| DCE-09 | the escape roots cross the pass boundary on the facts record (`Kb.with_attribution`) | drop `escape_roots` from `facts` | `carried` is empty → the chain is swept → length 2 fails |
