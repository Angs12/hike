# 03 — move test_vsa builders

Depends on: 02. Blocks: 04.

Move the top-level builders (mk_counter_loop, mk_flag_sub,
mk_caller_alias, mk_rsp_prologue_sub, mk_rsp_index_sub, and any other
`let mk_*` in test_vsa.ml) verbatim to test_common.ml; update call
sites. Signatures unchanged. Bar: 494 ok / 0 FAIL.
