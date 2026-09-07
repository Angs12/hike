# 06 — move test_properties builders (mk_when_chain + block locals)

Depends on: 05. Blocks: 07.

Move `mk_when_chain` and its local block builders (mk_store_blk,
mk_jmp_blk, mk_goto) to test_common.ml; update call sites.
Bar: 494 ok / 0 FAIL.
