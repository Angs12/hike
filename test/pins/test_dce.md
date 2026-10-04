# DCE pins

Module `Hike_dce` (`src/hike_dce.ml`), driven by
`test/unit/test_dce.ml` (ids `DCE-01`…).  Mechanism: plain liveness
over the model's read sets — the roots are every jump's reads
(`Model.jmp_reads`: the operand expressions plus the kind's ABI
boundary reads; a return edge reads the return registers and SP, a
call the parameter registers, the ABI return registers, and SP), and a
def or phi is live iff its lhs is read by a live node, to a fixpoint.
No keep arms, no escape roots.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| DCE-02 | the canonical direct return edge stands; the popped-address def dies; indirect-with-return and direct calls stay untouched | re-introduce the `mem[RSP]` load in the epilogue rewrite | the popped-address def survives → `t_gone` fails |
| DCE-03 | an ABI register def survives through the jump's boundary reads: a ret reads the return registers, a call the parameter registers and the return registers | drop the boundary reads from the roots (or the return regs from a call's reads) | `lhs_set` loses `RAX`/`RDI` → the check fails |
| DCE-04 | the two-tier region-mem rule: a fissioned store chain dies iff no Load roots it | make `region_mem` stores always live | `dead_count = 0` fails |
| DCE-05 | the sp/`frame_anchor` lane survives iff used; the unused sp-value def dies on both paths | keep every SP-derived def unconditionally | the `pn`/`cn` name lists change → fails |
| DCE-06 | a `Sub.intrinsic` sub passes through `dce` unchanged | run the sweep on intrinsic subs | the dead def is deleted → length 1 fails |
| DCE-07 | a never-read region-mem store chain is swept (the reads-only rule; an escaping store survives through the calls' boundary reads — the recorded increment) | root the mem var from a jmp's reads | the chain survives → length 0 fails |
| DCE-08 | a phi whose result no survivor reads is swept, and the operand defs cascade with it (the phi arm) | count phi reads as permanent (feed `perm` from `blk_reads`) | the phi and the `d8_v` defs survive → `phi_gone`/`v_gone` fail |
| DCE-09 | the sweep consumes no escape roots — the reads-only rule decides | root the store chain (a load or a jmp boundary read) | the chain survives → length 0 fails |
