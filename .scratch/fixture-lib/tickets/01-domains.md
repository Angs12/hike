# 01 — move test_domains builders (mk_mem)

Depends on: none. Blocks: 02 (linear chain — all tickets share test_common.ml).

Move the local `mk_mem ~key ~data` builder (test_domains.ml:458) to
top-level in test_common.ml; update its call sites (same file).
Bar: direct-exe runtest 494 ok / 0 FAIL.
