# Spec: Directional Infinite Sets in the VSA (Directional Strided Intervals)

Branch: `word-substrate` (or dedicated feature branch `directional-infs`)  
Spec Date: 2026-09-07  
Status: Spec Complete — Implementation Pending  

---

## 1. The Problem: Class 2 Semantic Failures

### 1.1 Machine-Verified Symptom
In the hike lifting pipeline, x86-64 ELF binaries are lifted to LLVM IR through value-set analysis (`cbat_vsa`). Across the 35 corpus binaries, exactly two binaries fail the semantic gate exclusively through the "Class 2" defect:
- `/tmp/corpus/variadic`, callee `sum_n(count, ...)`: lifted produces `sum = -883326090` (native `280`). The first 6 register-passed arguments are summed correctly; the 7th stack-spilled argument reads garbage.
- `/tmp/corpus/va_arg_vacopy`, callee `two_pass(count, ...)`: lifted produces `1 2 3 4 5 0` (native `1 2 3 4 5 6`), failing on the 6th variadic argument passed on the caller's stack frame.

### 1.2 The Failure Mechanism
1. **ABI Initialization:** Under the x86-64 System V ABI, `va_list.overflow_arg_area` is initialized to `RBP + 0x10`. Relative to callee entry `RSP = 0`, the pushed base pointer has coordinate `RBP = -8`, so `RBP + 0x10 = +8` — a strictly positive offset pointing directly into the caller's incoming argument area.
2. **Initial Store:** The pointer is stored to a stack cell (`mem[RBP - 0xC8] <- RAX`). At the store site, `rewrite_addr` (`src/cbat_vsa/cbat_vsa.ml:284`) resolves `RBP + 0x10` to the anchored constant `Int(+8)`. The cell at offset `-208` receives singleton `{+8}`.
3. **Loop Widening Destruction:** In the consumption loop, the pointer is loaded, dereferenced, advanced by 8 (`RDX := RAX + 8`), and written back to the cell. Across the loop back-edge, the cell value `{8}` joins with `{16}`, triggering `Clp.widen_join` (`src/cbat_vsa/cbat_clp.ml:1074`):
   ```ocaml
   else if subset p1 p2 then
     if equal p1 p2 then p1 else
     let step = step_of p2 in
     if W.is_zero step then top (bitwidth p2)
     else infinite ((base_of p2), step)
   ```
4. **Modulo Reduction Erases the Bound:** In `Clp.infinite` (`src/cbat_vsa/cbat_clp.ml:99`):
   ```ocaml
   let infinite (b, s) : t =
     ...
     let div, twos = factor_2s s in
     let step = W.div s div in
     let base = W.modulo b step in       (* 8 mod 8 = 0 *)
     let cardn = dom_size ~width:(width + 1) (width - twos) in
     create base ~step ~cardn
   ```
   For $b = 8, s = 8$, `base = 8 mod 8 = 0`. The set becomes `{0..0xFFFFFFFFFFFFFFF8}^inf`, representing all 8-aligned 64-bit words ($x \equiv 0 \pmod 8$). The lower bound $+8$ is erased.
5. **Channel 2 Rejection:** Channel 2 (`is_seed`, `src/cbat_vsa/cbat_vsa.ml:2896`) requires reloaded addresses to be a bounded, finite subset of the frame neighborhood (`-65536L, 65536L`). Because today's infinite set spans the entire 64-bit ring, `is_seed` rejects `is_infinite ws` (`cbat_vsa.ml:2909`).
6. **Downstream Cascade:** The deref `pad:64[mem[RAX]]` goes untagged $\implies$ `compute_sub_sig`'s `has_positive` (`src/hike.ml:154`) does not fire $\implies$ `hike_stack` parameter is not granted $\implies$ `bil2llvm.ml` emits pointer arithmetic relative to the callee's own uninitialized frame rather than rebasing to `hike_stack + offset`.

---

## 2. Theoretical Foundations & Academic Literature

Static binary analysis contains two fundamental interval paradigms:

| Literature | Domain | Infinite Representation | Widening Behavior |
| :--- | :--- | :--- | :--- |
| **Balakrishnan & Reps** (*CC 2004*, *ACM TOPLAS 2010* "WYSINWYX") | Strided Intervals (SI) $s[l, u]$ on $\mathbb{Z} \cup \{-\infty, +\infty\}$ | **Directional**: $[l, +\infty)$, $(-\infty, u]$ | **Stable-bound widening**: If $l_1 = l_2$ and $u_2 > u_1$, retain $l_1$ and extrapolate $u \to +\infty$. |
| **Philippe Granger** (*IJCM 1989*); **Draper CBAT CLP** | Arithmetical congruences / circular linear progressions | **Modular residue class**: $b + s\mathbb{Z}_{2^w}$ with $b = b \bmod s$ | **Collapse to residue class**: Normalizes base mod step, destroying directionality. |
| **Navas, Schachte, Søndergaard, Stuckey** (*APLAS 2012*, *ACM TOPLAS 2015*) | Wrapped Strided Intervals (WSI) on $\mathbb{Z}_{2^w}$ | **Directed circular arcs**: Distinguishes non-wrapping paths from full circular wraps | Preserves directional bounds until unsigned/signed modular wrap occurs. |

### Why Simon & King Landmarks Cannot Solve This
Hike implements Simon & King (*"Widening Polyhedra with Landmarks"*, APLAS 2006) in the words lane. However:
1. Memory cells carry no landmarks by design (`MemEnv.widen_join` in `cbat_ai_representation.ml:289`).
2. Landmark acquisition (`observe_unsat`) requires a conditional comparison. Variadic overflow pointers are walked unconditionally until a separate counter or format-string loop terminates. The pointer is never compared against a bound, so no landmark can ever be acquired for it.

### The Hike Solution
Extend `Clp.t` to bridge both paradigms: support **directional infinite rays** (`Ascending`, `Descending`) alongside **modular residue classes** (`Circular`). Pointers and loop counters retain their non-negative origin $lo$ as an `Ascending` ray, while wrapping operations fall back to `Circular`.

---

## 3. Decisions (Grilling-Settled Principles)

1. **Domain-Level Fix Over Ad-Hoc Seeding Hacks:**  
   Rejected Design 2 (heuristic seeding) and Design 4 (AST pattern matching / syntactic def-use lookback). The fix must live in the abstract domain (`cbat_clp.ml`), maintaining soundness and monotonic properties.
2. **Direction as an Explicit 4-Way Sum Type:**  
   Replace boolean `is_inf : bool` with:
   ```ocaml
   type direction =
     | Finite
     | Ascending   (* Bounded below by base; step > 0; unconstrained above *)
     | Descending  (* Bounded above by base; step > 0; unconstrained below *)
     | Circular    (* Full residue class modulo step; base = base mod step *)
   [@@deriving bin_io, sexp, compare]
   ```
3. **Sound Fallback to Circular on Wraparound:**  
   In modular arithmetic, if an `Ascending` ray overflows the word boundary ($base + k \cdot step$ wraps past $2^w - 1$), it soundly falls back to `Circular`. Linear ray precision is preserved whenever execution remains non-wrapping.
4. **Stable-Bound Widening:**  
   `widen_join` must inspect the stable bounds of its operands: if lower bound is unchanged and upper bound increased, the result is `Ascending`.
5. **No Regressions on the 33 Passing Binaries:**  
   All 33 non-variadic binaries must remain byte-identical or strictly improved (more tagged stack accesses, 0 regressions in semantic passes).

---

## 4. Mathematical Specification of `Clp.t`

### 4.1 Type Definition
```ocaml
type direction =
  | Finite
  | Ascending
  | Descending
  | Circular
[@@deriving bin_io, sexp, compare]

type t = {
  base : word;
  step : word;
  cardn : word;
  dir : direction;
}
[@@deriving bin_io, sexp, compare]
```

### 4.2 Semantic Concretization $\gamma(p)$
For bitwidth $w$, let $W = \mathbb{Z}/2^w\mathbb{Z}$:
- **$\gamma(\text{Finite}):$** $\{ (p.base + n \cdot p.step) \bmod 2^w \mid 0 \le n < p.cardn \}$
- **$\gamma(\text{Ascending}):$** $\{ p.base + n \cdot p.step \mid n \ge 0 \text{ and } p.base + n \cdot p.step \le 2^w - 1 \}$.  
  Strict lower bound: $\min \gamma(p) = p.base$.
- **$\gamma(\text{Descending}):$** $\{ p.base - n \cdot p.step \mid n \ge 0 \text{ and } p.base - n \cdot p.step \ge 0 \}$.  
  Strict upper bound: $\max \gamma(p) = p.base$.
- **$\gamma(\text{Circular}):$** $\{ x \in W \mid x \equiv p.base \pmod{p.step} \}$ where $p.base = p.base \bmod p.step$.

### 4.3 Canonical Representation
- **Bottom:** $cardn = 0 \implies base = 0, step = 0, cardn = 0, dir = Finite$.
- **Singleton:** $cardn = 1 \implies step = 0, dir = Finite$.
- **Ascending Ray:** $step > 0$. $cardn = 1 + \lfloor (2^w - 1 - base) / step \rfloor$. If $cardn = 1$, canonicalize to `Finite`.
- **Descending Ray:** $step > 0$. $cardn = 1 + \lfloor base / step \rfloor$. If $cardn = 1$, canonicalize to `Finite`.
- **Circular:** $base = base \bmod step$. $step$ is factored into a power of 2 ($step = 2^k$). $cardn = 2^{w-k}$.
- **Top:** `Circular` with $base = 0, step = 1, cardn = 2^w$.

---

## 5. Operations Specification

### 5.1 `widen_join (p1 : t) (p2 : t) : t`
```ocaml
let widen_join (p1 : t) (p2 : t) : t =
  if is_bottom p1 then top (bitwidth p2)
  else if subset p1 p2 then
    if equal p1 p2 then p1
    else
      let width = bitwidth p2 in
      let step = step_of p2 in
      if W.is_zero step then top width
      else
        match min_elem p1, max_elem p1, min_elem p2, max_elem p2 with
        | Some lo1, Some hi1, Some lo2, Some hi2 ->
          let lo_stable = W.(=) lo1 lo2 in
          let hi_stable = W.(=) hi1 hi2 in
          let hi_grew = W.(>) hi2 hi1 in
          let lo_grew = W.(<) lo2 lo1 in
          if lo_stable && hi_grew then
            create_ascending ~width ~base:lo1 ~step
          else if hi_stable && lo_grew then
            create_descending ~width ~base:hi1 ~step
          else
            infinite ((base_of p2), step)
        | _ -> infinite ((base_of p2), step)
  else join p1 p2
```

### 5.2 `min_elem` and `max_elem`
```ocaml
let min_elem (p : t) : word option =
  if is_bottom p then None
  else match p.dir with
  | Finite -> nearest_succ (W.zero (bitwidth p)) p
  | Ascending -> Some p.base
  | Descending -> Some (W.modulo p.base p.step)
  | Circular -> nearest_succ (W.zero (bitwidth p)) p

let max_elem (p : t) : word option =
  if is_bottom p then None
  else match p.dir with
  | Finite -> nearest_pred (W.ones (bitwidth p)) p
  | Ascending ->
    let max_wd = W.ones (bitwidth p) in
    let diff = W.sub max_wd p.base in
    let rem = W.modulo diff p.step in
    Some (W.sub max_wd rem)
  | Descending -> Some p.base
  | Circular -> nearest_pred (W.ones (bitwidth p)) p
```

### 5.3 `subset (p1 : t) (p2 : t) : bool`
Must handle cross-direction subset without wrapping-end false positives:
- `Finite ⊆ Ascending`: $\min(p_1) \ge p_2.base \land p_2.step \mid p_1.step \land (\min(p_1) - p_2.base) \equiv 0 \pmod{p_2.step}$.
- `Finite ⊆ Descending`: $\max(p_1) \le p_2.base \land p_2.step \mid p_1.step \land (p_2.base - \max(p_1)) \equiv 0 \pmod{p_2.step}$.
- `Ascending ⊆ Ascending`: $p_1.base \ge p_2.base \land p_2.step \mid p_1.step \land (p_1.base - p_2.base) \equiv 0 \pmod{p_2.step}$.
- `Descending ⊆ Descending`: $p_1.base \le p_2.base \land p_2.step \mid p_1.step \land (p_2.base - p_1.base) \equiv 0 \pmod{p_2.step}$.
- `(Ascending | Descending | Finite) ⊆ Circular`: $p_2.step \mid p_1.step \land (base_1 - p_2.base) \equiv 0 \pmod{p_2.step}$.
- `Circular ⊆ (Ascending | Descending | Finite)`: `false`.
- `(Ascending | Descending) ⊆ Finite`: `false`.
- `Ascending ⊆ Descending` and `Descending ⊆ Ascending`: `false`.

### 5.4 `intersection (p1 : t) (p2 : t) : t` (Meet)
- `Ascending ⊓ Finite`: Truncates the ray into a bounded `Finite` interval $[\max(lo_1, lo_2), hi_2]$ on the grid.
- `Ascending ⊓ Ascending`: Stride becomes $\text{lcm}(s_1, s_2)$. Lower bound becomes first grid point $\ge \max(lo_1, lo_2)$ via Diophantine solve.
- `Ascending ⊓ Descending`: Bounded `Finite` interval if $lo_{\text{asc}} \le hi_{\text{desc}}$, else $\bot$.

### 5.5 `translate (p : t) (i : word) : t`
- `Ascending`: $base' = base + i$. If unsigned overflow occurs ($base' < base \land i > 0$), fallback to `infinite(base', step)`. Else `create_ascending base' step`.
- `Descending`: $base' = base + i$. If unsigned underflow occurs, fallback to `infinite(base', step)`.
- `Circular`: $base' = base + i \implies infinite(base', step)$.

---

## 6. Pipeline Integration & Consumer Updates

### 6.1 `src/cbat_vsa/cbat_clp_set_composite.ml`
Expose directional predicates in `WordSet`:
- `is_ascending : t -> bool`
- `is_descending : t -> bool`
- `is_circular : t -> bool`

### 6.2 `src/cbat_vsa/cbat_vsa.ml`
1. **Channel 2 Seeding (`is_seed`, line 2896):**
   ```ocaml
   match WordSet.min_elem ws, WordSet.max_elem ws with
   | Some lo, Some hi -> (
       match Word.to_int64 lo, Word.to_int64 hi with
       | Ok lo_i64, Ok hi_i64 ->
         let nlo, nhi = frame_neighborhood in
         if WordSet.is_circular ws then false
         else if WordSet.is_ascending ws then
           (* Non-negative ascending ray pointing into caller stack frame *)
           lo_i64 >= 0L && lo_i64 <= nhi
         else
           lo_i64 >= nlo && hi_i64 <= nhi
       | _ -> false)
   | _ -> false
   ```
2. **Classification (`classify`, line 2820):**
   `min_elem` on `Ascending { base = 8; step = 8 }` produces `Some 8`. `classify` emits `Infinite (8L, hi_i64)`.

### 6.3 `src/convutils.ml` & `src/bil2llvm.ml`
1. `is_positive_kind` (`convutils.ml:149`): Evaluates $lo > 0\text{L}$. With $lo = 8\text{L}$, it returns `true`.
2. `compute_sub_sig` (`hike.ml:154`): `has_positive` fires $\implies$ grants `hike_stack` parameter to the callee.
3. `rebase_addr` (`bil2llvm.ml:887`): Positive `Infinite` tag rebases the pointer dereference onto `hike_stack + offset`, loading the caller's stack arguments directly.

---

## 7. Work Plan & Tracer-Bullet Tickets

### Ticket 1: Referee & Differential Harness (`zz_scratch_probe/clpequiv.ml`)
- Add property tests in `clpequiv.ml` for `direction` variants.
- Test stable-bound widening on synth fixture $\{8\} \nabla \{8, 16\} = \text{Ascending}(8, 8)$.
- Verify subset, intersection, and translate properties.

### Ticket 2: CLP Domain Representation (`src/cbat_vsa/cbat_clp.ml`)
- Implement `type direction = Finite | Ascending | Descending | Circular`.
- Implement canonical constructors `create_ascending`, `create_descending`, `create_circular`.
- Update `min_elem`, `max_elem`, `min_elem_signed`, `max_elem_signed`.

### Ticket 3: CLP Operations (`src/cbat_vsa/cbat_clp.ml`)
- Implement stable-bound `widen_join`.
- Implement directional `subset`, `equal`, `compare`.
- Implement `intersection` (meet) and `translate`.

### Ticket 4: Composite Lifting & VSA Seeding (`cbat_clp_set_composite.ml` & `cbat_vsa.ml`)
- Expose direction predicates in `WordSet`.
- Update `is_seed` (Channel 2) to admit non-negative `Ascending` rays.
- Verify `classify` emits `Infinite (lo, hi)` with $lo \ge 8\text{L}$.

### Ticket 5: Validation & Gate Battery
- `dune runtest` green (467+ tests).
- `zz_scratch_probe/vsa_ptr_diag.exe` on `variadic:sum_n` and `va_arg_vacopy:two_pass` confirms `mem[RAX]` is tagged `Infinite(8L, ...)`.
- Full corpus emission 35/35 rc=0.
- `scripts/semantic/run_semantic_all.sh` verifies:
  - `variadic` flips to **PASS** (`sum = 280`).
  - `va_arg_vacopy` flips to **PASS** (`1 2 3 4 5 6`).
  - All 33 other binaries remain byte-identical.
- `scripts/check_allocas.sh` passes 100% (160/160 checks).

---

## 8. Non-Goals
1. **Full Polyhedral Domain:** We are not adding relational polyhedra; directional strided intervals are non-relational rays.
2. **Arbitrary Stride Alignment on Decrements:** Descending rays are bounded above by $base$ and bounded below by $0$ in unsigned space.
3. **Changing the Words Lane Landmark Engine:** Landmarks remain active in words; directional CLPs provide the non-relational ray baseline for memory and unconstrained induction variables.
