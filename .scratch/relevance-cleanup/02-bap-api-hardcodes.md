# 02 — BAP-API hardcodes (Q6 1-2-3-5)

**Depends on:** 01
**Blocks:** 03

Replace hardcodes `1-2-3-5` with BAP API, esp. SP via `Targetutils.sp`.

Tasks:
- Delete `is_arg_setup` hardcode `hike_vsa_relevance.ml:146-153` from relevance (moved out; only stays relevant if it flows into `stack_access`).
- Replace `alloc_rhs` `hike_vsa_relevance.ml:163-166` and indirect VLA `hike_vsa_relevance.ml:174-178` `Bil.BinOp(MINUS, Var a, size)` + `Bil.Int _` checks with `Exp.mapper`/`Term.visitor` shape via `Targetutils.sp`, no `"RSP"` strings.
- Replace `"RSP"`/`"RBP"` string checks in `hike_vsa_relevance.ml:94` seed and `Var.base` plumbing with `Targetutils.sp` helper.
- Centralize `is_stack_access` shape `Load/Store/Cast-Load/Cast-Store` into one `is_stack_load_store : exp -> bool` helper used as `stack_access` predicate (single source for `hike_vsa.ml:60` / `bil2llvm.ml:739` future reuse).

Gate: `dune runtest` + corpus `bap --pass=hike-convlir` 31/31 still green; tag diff vs pre-change shows only intentional VLA/arg-setup de-tagging.
