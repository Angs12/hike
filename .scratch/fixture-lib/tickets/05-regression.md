# 05 — move test_regression builders (mk_c3, mk_store)

Depends on: 04. Blocks: 06.

Move `mk_c3` and the local `mk_store lo data sz` (MINUS/rsp-rooted)
to test_common.ml as `mk_c3` and `mk_store_minus` (distinct name per
the no-unification decision); update call sites. Bar: 494/0.
