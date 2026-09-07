# 02 — move test_seed builders (mk_state)

Depends on: 01. Blocks: 03.

Move the local `mk_state` AI-state builder (test_seed.ml:24) to
top-level in test_common.ml; update its call sites (same file).
Bar: direct-exe runtest 494 ok / 0 FAIL.
