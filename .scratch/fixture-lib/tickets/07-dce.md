# 07 — move test_dce builders (mk_store, mk_sub)

Depends on: 06. Blocks: 08.

Move the local `mk_store off dat` (PLUS/base-rooted, fixed `r64`)
to test_common.ml as `mk_store_plus`, and the local `mk_sub nm`;
update call sites. Bar: 494 ok / 0 FAIL.
