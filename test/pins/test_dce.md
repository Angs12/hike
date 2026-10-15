# DCE pins

Module `Hike_dce` (`src/hike_dce.ml`), driven by
`test/unit/test_dce.ml`. Loads and stores are permanent liveness roots,
including nested expressions. Their scalar and memory dependencies propagate
through the ordinary def/phi fixpoint alongside ABI and escape roots.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| DCE-13 | all written global and local storages survive without a reader | remove the relevant liveness root | the retained operation or carried fact disappears |
| DCE-02 | return/call transfers stay unchanged and the unused popped-address load survives | remove the relevant liveness root | the retained operation or carried fact disappears |
| DCE-03 | an ABI register def survives through the jump's boundary reads: a ret reads the return registers, a call the parameter registers and the return registers | drop the boundary reads from the roots (or the return regs from a call's reads) | `lhs_set` loses `RAX`/`RDI` → the check fails |
| DCE-04 | region store chains survive with and without a reader | remove the relevant liveness root | the retained operation or carried fact disappears |
| DCE-05 | the sp/`frame_anchor` lane survives iff used; the unused sp-value def dies on both paths | keep every SP-derived def unconditionally | the `pn`/`cn` name lists change → fails |
| DCE-06 | a `Sub.intrinsic` sub passes through `dce` unchanged | run the sweep on intrinsic subs | the dead def is deleted → length 1 fails |
| DCE-08 | a phi whose result no survivor reads is swept, and the operand defs cascade with it (the phi arm) | count phi reads as permanent (feed `perm` from `blk_reads`) | the phi and the `d8_v` defs survive → `phi_gone`/`v_gone` fail |
| DCE-09 | attribution carries escape roots through the facts record | remove the relevant liveness root | the retained operation or carried fact disappears |
| DCE-10 | a call-bearing block's argument temps are the call's boundary reads. | textually invert the pinned contract in `Hike_dce` | pin FAILs under that inversion (re-demonstrated by review) |
| DCE-11 | a store into an escape-rooted storage survives with no in-sub reader. | textually invert the pinned contract in `Hike_dce` | pin FAILs under that inversion (re-demonstrated by review) |
| DCE-12 | a store into the global memory state survives with no in-sub reader. | textually invert the pinned contract in `Hike_dce` | pin FAILs under that inversion (re-demonstrated by review) |
