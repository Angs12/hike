# Pins — test_split_blocks

Module: `test/unit/test_split_blocks.ml` (group `split_blocks`, ids
`SBLK-01`…`SBLK-05`).  Production mechanism: `src/hike_split_blocks.ml`
(the `hike-split-blocks` pass, chained after `hike-sections`), plus
`src/bil2llvm.ml`'s `create_branches` (the terminal-guard false edge) —
its pins live here because the two rules are one contract: the BIR term
order is the fallthrough semantics.

Fixtures are hand-built BIR; no emitter runs in this module (the
emitter-side pins are EMIT-21/EMIT-30/EMIT-31 in `test_bil2llvm.md`).
Every pin builds its own sub inside its closure.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| SBLK-01 | `split_sub` expands a direct-goto jmp series to one block per jmp, pieces consecutive in term order, each piece's jmp targeting the original target; `fallthrough` walks the term order. | In `pieces`, return `[ blk ]` unchanged (never splice pieces). | SBLK-01 FAILs: the sub keeps 4 blocks (not 7) and the fallthrough chain is `None`/the original successor only. |
| SBLK-02 | Piece 1 is `Term.filter jmp_t` of the original block (tid, defs, phis, and the `address` attr survive); pieces 2..N are `Blk.create` bare blocks. | In `pieces`, build piece 1 with `Blk.create` too (fresh tid, empty dict). | SBLK-02 FAILs: piece 1 loses the original tid/def/phi/attr. |
| SBLK-03 | Blocks with at most one jmp are identity: same block tid sequence, same count. | In `split_sub`, split N=1 blocks too (drop the `> 1` filter). | SBLK-03 FAILs: the tid sequence grows. |
| SBLK-04 | A series holding an indirect jmp is left whole with one `hike: split-blocks:` warning naming sub and block. | In `split_sub`, drop the `compilable_series` check (split any multi-jmp block). | SBLK-04 FAILs: the warning is absent and the tid sequence grows. |
| SBLK-05 | `free_regs` reads liveness over the rendered CFG (explicit targets + guarded-terminal fallthroughs): a piece's in-edge is the previous piece's fallthrough, so a guard var defined in the series block stays out of the free set. | In `Hike_split_blocks.free_regs`, read the entry set off `Sub.free_vars` instead (the BAP tid graph glues every in-degree-0 piece to start). | SBLK-05 FAILs: the free set gains `sb5_x` (the piece bypass). |
