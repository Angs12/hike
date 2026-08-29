# 03 — Consumer dedup (Q7 + Q11)

**Depends on:** 01, 02
**Blocks:** 04

Make `Hike_vsa_relevance.has_stack_access` / `is_sp` the single source; delete scattered reimplementations (Q7 a+b).

Tasks:
- `src/hike_vsa.ml:52-139,345-365` — replace `Term.has_attr d Relevance.direct_sp` + `String.equal n "RSP"/"RBP"` `pointer_value_addr` with `Hike_vsa_relevance.has_stack_access` and `Hike_vsa_relevance.is_sp`.
- `src/hike_stack_to_locals.ml:207-281` — replace `String.equal (Var.name v) "RSP"` in `is_abi_visible` and `has_attr direct_sp` checks with `has_stack_access`.
- `src/bil2llvm.ml:739-751,750,1650` — delete `addr_is_stack` recalculation and `is_sp_or_fp` `String.equal "RSP"/"RBP"` helpers; use `has_stack_access` tag query. `RBP` no longer participates in relevance seed (GPR).
- `src/hike_dce.ml:54` `is_sp` stays but re-exports via `Hike_vsa_relevance.is_sp` or is removed if duplicate.

Gate: `grep -r "String.equal.*RSP" src/` hits only `cbat_vsa` legacy frame code + `Targetutils` fallback; no probe in `hike_*` except `targetutils.ml`.
