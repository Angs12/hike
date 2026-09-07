# 04 — move test_backward's 15 loop builders

Depends on: 03. Blocks: 05.

Move all 15 top-level `mk_*` builders (mk_l3a_loop, mk_l3c1_loop,
mk_l3c2_loop, mk_l3c3_loop, mk_l3c4_loop, mk_l3c4_vv_loop,
mk_l3c5_loop, mk_l3b1_loop, mk_l3b4_diamond, mk_l39_loop,
mk_l39b5_loop, mk_e1_loop_sub, mk_e1_flat_sub, mk_l6_rbp_loop,
mk_r2_loop) verbatim to test_common.ml; update call sites.
Signatures unchanged. Bar: 494 ok / 0 FAIL.
