# 04 — Composite Lifting & VSA Seeding

**Status:** ready-for-agent  
**Depends on:** 03  
**Blocks:** 05  

**READ FIRST:**
- The spec: `.scratch/directional-infs/spec.md` (§6)
- Consumer files:
  - `src/cbat_vsa/cbat_clp_set_composite.ml`
  - `src/cbat_vsa/cbat_vsa.ml` (`is_seed` at line ~2896, `classify` at line ~2820)
  - `src/convutils.ml` (`is_positive_kind` at line ~149)

**Tasks:**
- [ ] In `src/cbat_vsa/cbat_clp_set_composite.ml`:
  - Expose directional predicates in module `WordSet`:
    - `is_ascending : t -> bool`
    - `is_descending : t -> bool`
    - `is_circular : t -> bool`
  - Ensure `clp_diff_finset` preserves directional bounds during guard meets and producer subtractions.
- [ ] In `src/cbat_vsa/cbat_vsa.ml`:
  - Update `is_seed` (Channel 2):
    ```ocaml
    if WordSet.is_circular ws then false
    else if WordSet.is_ascending ws then
      lo_i64 >= 0L && lo_i64 <= nhi
    else
      lo_i64 >= nlo && hi_i64 <= nhi
    ```
  - Verify `classify` passes `WordSet.min_elem ws` as `lo`, yielding `Infinite (8L, hi)` for `Ascending { base = 8; step = 8 }`.
- [ ] Verify `is_positive_kind` in `src/convutils.ml` correctly recognizes `Infinite (8L, hi)` as positive ($8\text{L} > 0\text{L}$).

**Verification:**
- Run `zz_scratch_probe/vsa_ptr_diag.exe -- /tmp/corpus/variadic sum_n`:
  - `DEF %000007fe` must now report `ch2=true(Ascending...)` and `tag=Infinite(8, ...)`.
- Run `zz_scratch_probe/vsa_ptr_diag.exe -- /tmp/corpus/va_arg_vacopy two_pass`:
  - `DEF %0000093c` must report `ch2=true(Ascending...)` and `tag=Infinite(8, ...)`.
