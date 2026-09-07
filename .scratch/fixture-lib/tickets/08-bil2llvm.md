# 08 — move test_bil2llvm builders (mk_exit_blk, mk_fp_*)

Depends on: 07. Blocks: none (last).

Move `mk_exit_blk`, `mk_fp_call_sub`, `mk_fp_stub`,
`mk_fp_program`, and the local `mk_sub nm` to test_common.ml;
update call sites. Note `mk_exit_blk` becomes shared vocabulary for
the edge-case wing (candidate #6). Bar: 494 ok / 0 FAIL, then final
`dune runtest` green + name-collision audit per the spec.
