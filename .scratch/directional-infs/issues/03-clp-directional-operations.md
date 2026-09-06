# 03 — CLP Directional Operations: Widening, Meet, Subset, Translate

**Status:** completed
**Depends on:** 02  
**Blocks:** 04  

**READ FIRST:**
- The spec: `.scratch/directional-infs/spec.md` (§5)
- Domain file: `src/cbat_vsa/cbat_clp.ml` (`widen_join`, `subset`, `intersection`, `translate`, `join`, `equal`, `compare`)

**Tasks:**
- [x] In `src/cbat_vsa/cbat_clp.ml`:
  - **`widen_join`:** Implement stable-bound detection:
    - If `lo1 = lo2` and `hi2 > hi1` $\implies$ `create_ascending ~width ~base:lo1 ~step`.
    - If `hi1 = hi2` and `lo2 < lo1` $\implies$ `create_descending ~width ~base:hi1 ~step`.
    - Otherwise (both bounds shifted, or wrap occurred) $\implies$ `infinite ((base_of p2), step)`.
  - **`subset`:** Implement cross-direction containment:
    - `Finite ⊆ Ascending`, `Finite ⊆ Descending`, `Ascending ⊆ Ascending`, etc.
    - `Circular ⊆ (Ascending | Descending)` is always `false`.
    - Directional ray ⊆ `Circular` is `true` iff stride divides and bases align mod step.
  - **`intersection` (Meet):**
    - `Ascending ⊓ Finite`: Truncate ray to `Finite` interval $[\max(lo_1, lo_2), hi_2]$ on the grid.
    - `Ascending ⊓ Ascending`: Merge strides via LCM and solve joint base.
    - `Ascending ⊓ Descending`: Bounded `Finite` range if $lo_{\text{asc}} \le hi_{\text{desc}}$, else bottom.
  - **`translate`:**
    - `Ascending`: $base' = base + i$. If unsigned overflow wraps past $2^w - 1$, demote to `infinite(base', step)`. Else `create_ascending`.
    - `Descending`: $base' = base + i$. If unsigned underflow wraps below $0$, demote to `infinite(base', step)`.
  - **`equal` and `compare`:** Update structural equality and comparison to consider `dir`.

**Verification:**
- `dune runtest` passes with CBAT suite 100% green.
- `zz_scratch_probe/clpequiv.exe` confirms algebraic laws hold on all directional combinations.
