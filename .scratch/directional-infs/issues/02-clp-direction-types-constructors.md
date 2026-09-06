# 02 — CLP Direction Types and Constructors

**Status:** ready-for-agent  
**Depends on:** 01  
**Blocks:** 03  

**READ FIRST:**
- The spec: `.scratch/directional-infs/spec.md` (§3, §4)
- Domain file: `src/cbat_vsa/cbat_clp.ml` (inspect `type t`, `create`, `infinite`, `dom_size`)

**Tasks:**
- [ ] In `src/cbat_vsa/cbat_clp.ml`:
  - Define `type direction = Finite | Ascending | Descending | Circular [@@deriving bin_io, sexp, compare]`
  - Update `type t` to:
    ```ocaml
    type t = {
      base : word;
      step : word;
      cardn : word;
      dir : direction;
    }
    [@@deriving bin_io, sexp, compare]
    ```
  - Define `create_ascending ~width ~base ~step` and `create_descending ~width ~base ~step` enforcing canonical form:
    - If `cardn = 1`, normalize to `Finite` singleton with `step = 0`.
    - If `cardn = 0`, normalize to `bottom`.
  - Update `infinite (b, s)` to create `dir = Circular` with `base = W.modulo b step` (preserving full backward compatibility for circular congruences).
  - Update `min_elem`, `max_elem`, `min_elem_signed`, `max_elem_signed` to handle `Ascending` (returning `Some p.base` as lower bound) and `Descending` (returning `Some p.base` as upper bound).
- [ ] Ensure all existing constructors (`create`, `top`, `bottom`, `of_word`) initialize `dir` appropriately (`Finite` or `Circular`).
- [ ] `dune build` compiles cleanly.

**Verification:**
- `dune build` and `dune runtest` pass with no regressions on existing tests.
