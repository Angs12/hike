# Pins — test_split_blocks

Module: `test/unit/test_split_blocks.ml` (group `split_blocks`, ids
`SBLK-03`…`SBLK-08`).  Production mechanism: `src/hike_split_blocks.ml`
(the `hike-split-blocks` pass, chained after `hike-sections`) — it
materializes every guard's implicit fallthrough as an explicit `Goto`
and splits a 3+-jmp direct-goto series into pieces, each carrying an
explicit `Goto` to the next.  The BIR's edges are then the jmps
themselves, so `src/bil2llvm.ml`'s `create_branches` is a mechanical
1- or 2-jmp mapping and every later pass (SSA, types) reads
`Sub.to_graph`.  Its pins live here because the split and the emitter's
branch shape are one contract: the BIR is explicit.

Fixtures are hand-built BIR; no emitter runs in this module (the
emitter-side pins are EMIT-21/EMIT-30/EMIT-31/EMIT-33 in `test_bil2llvm.md`).
Every pin builds its own sub inside its closure.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| SBLK-03 | Blocks with at most two jmps are identity: same block tid sequence, same count. | In `split_sub`, split at the `> 2` threshold too (drop it to `> 1`). | SBLK-03 FAILs: the tid sequence grows. |
| SBLK-04 | A 3+-jmp series holding an indirect jmp is left whole with one `hike: split-blocks:` warning naming sub and block. | In `split_sub`, drop the `compilable_series` check (split any 3+-jmp block). | SBLK-04 FAILs: the warning is absent and the tid sequence grows. |
| SBLK-05 | `free_regs` reads liveness over the BIR's explicit edges: a piece's in-edge is the previous piece's explicit `Goto`, so a guard var defined in the series block stays out of the free set. | In `Hike_split_blocks.free_regs`, read the entry set off `Sub.free_vars` instead. | SBLK-05 FAILs: the free set gains `sb5_x`. |
| SBLK-08 | A dispatch word naming an in-sub block that the arming phase (`arm_dispatches`) did not arm is ruled into `series` under its own case test — a destination, never a failure. | In `series`, restore the `Goto (Direct t) -> failwith` arm. | SBLK-08 FAILs: `materialize` raises `Failure` instead of emitting the arm to the target. |
| SBLK-06 | a bounded indirect call becomes one direct arm per named sub start. | textually invert the pinned contract in `Hike_split_blocks` | pin FAILs under that inversion (re-demonstrated by review) |
| SBLK-07 | a bounded target with no naming-map entry fails loudly. | textually invert the pinned contract in `Hike_split_blocks` | pin FAILs under that inversion (re-demonstrated by review) |
