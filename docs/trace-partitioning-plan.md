# Trace-Partitioning Plan — Single-Pass Design (authoritative spec)

> **Status (2026-08-29).** This document is the single source of truth for the
> VSA's backward-refinement / trace-partitioning design. It was previously
> cited by `§`-numbers in code comments (`cbat_vsa.ml`, `cbat_ai_memmap.ml`,
> `hike_vsa.ml`) but did **not exist on disk** — only its §-references survived.
> This version rewrites it to match the **fused single-pass architecture**
> decided in the grilling session of 2026-08-29.
>
> **Headline decision:** the two-phase design (forward WTO fixpoint **+ Phase B
> post-pass** `edge_views_of` → `refine_edge` → `partitioned_states`) is
> **replaced by one coupled pass**. Phase B is deleted. The deep backward walk
> is *not* deleted — it is **moved inline** and becomes the per-edge transfer
> at each conditional jump.

---

## 1. Goal and vocabulary

- **Trace-partitioning** — making a block's *entry* abstract state aware of
  *which incoming edge* (hence which branch condition) it arrived on, so the
  analysis is **branch-sensitive** rather than branch-blind.
- **Edge-splitting** — at a conditional jump, computing two refined successor
  inputs (taken refined by `c`, fallthrough refined by `¬c`) and transferring
  each to its correct destination block.
- **Inverse denotation (deep walk)** — the backward derivation of a block's
  *pre-state* from a post-edge constraint, via producer subtraction
  (`cstr' = cstr ∩ post(v)`) and trace-exact cell meets. This is what
  `refine_edge` computes; it is invoked **inline at the jump**.
- **TAG state** — a per-block abstract state already refined by its incoming
  edge conditions. Historically produced by `partitioned_states`; in the
  single-pass design this is simply the block's **IN-state in the solution**.

---

## 2. Architecture (single coupled pass)

The forward engine (`static_graph_vsa`, a Bourdoncle WTO fixpoint) is unchanged
in its iteration/widening structure. The only change is **what happens at a
jump**:

1. `denote_block_with_stores` computes `postcond = denote_defs b env`, then
   calls `denote_jump`.
2. In `denote_jump`, for a **`Bil.If(c, t, f)`** jmp:
   - derive the True/False constraint lists via `edge_constraints`;
   - run `refine_edge` for the `P→t` edge (True side) and the `P→f` edge
     (False side = complement);
   - join each refined env into the destination block's IN-state.
3. For an **unconditional `Jmp` / `Call`**: identity — `S.in ⊔= P.out`
   (no refine). Calls keep their existing frame-keeping call abstraction.

`static_graph_vsa_with_views` is renamed (drops `_with_views`) and returns
just `sol` — there is no `views` value anymore.

---

## 3. The refinement — deep backward walk (the "inverse denotation")

`refine_edge(edge, cstr)` runs a **reverse-CFG fixpoint**
(`Cbat_contextual_fixpoint.fixpoint ~rev:true`) rooted at the edge's source
block. For each live variable it uses:

- **`reverse_def_walk`** (producer subtraction):
  `cstr' = cstr ∩ post(v)`, where
  `post(v) = denote_def d (Solution.get sol (tid blk))`; the lhs is dropped
  from the live set when the meet is empty.
- **`def_constraints` / `operand_constraints`** — per-def / per-operand
  backward constraint derivation.
- **`constrain_cell_on_trace`** — the *cell-gate replacement*: the rewritten
  address's load state, intersected with the live constraints, is met into the
  cell via `Mem.meet_range`.

This reaches **every upstream live variable**, not just the guard variable. It
is the exact mechanism `partitioned_states` used to derive the per-edge TAG
states; it is now invoked at the jump instead of in a post-pass.

---

## 4. Edge constraints — the two refinements

`edge_constraints` decomposes a guard into `Var` / `Cell` / `Infeasible` seeds
for **both** the True and False sides:

- **True side** — `c`, decoded by `decoded_condition` (recognises the `jle`→
  `SLE`, `jl`→`SLT`, `ja`→`UGT` compound -O0 flag idioms) and realised by
  `decoder_constraint` (all nine rows: `ULT/ULE/EQ/SLT/SLE/UGT/UGE/SGT/SGE`).
- **False side** — `complement_guard_op(c)` (e.g. `NEQ` → `EQ`).

Transfer (the edge-split):

```
t.in ⊔= refine_edge(edge P→t, True-cstr)    # taken, refined by c
f.in ⊔= refine_edge(edge P→f, False-cstr)   # fallthrough, refined by ¬c
# raw P.out is NOT separately joined — joining both would collapse to raw
```

**NEQ / non-convex guards:** `comparison_constraint` returns `None` on the
True side, so the *taken* edge gets **identity** and the fallthrough gets the
`EQ` interval. This is the inherited -O2 `w_big` loop-counter limitation; it is
**not a regression** of this change.

---

## 5. Widening and landmarks

- Refined states flow through the **existing widen-at-head machinery unchanged**:
  `widen_join` at WTO heads after 10 outer sweeps. No special widening for
  refined states.
- **Landmark acquisition is preserved by construction**: the walk's meets fire
  `observe_unsat_var` (inside `meet_var` / `Mem.meet_range`), and
  `Cbat_landmarks.widening_at_head` is already bound around
  `denote_block_with_stores` (so active during the inline walk).
- `assume_jump_cond_with_group`'s shallow `apply_operand_constraint` pre-step
  is **subsumed** by the deep walk; its landmark-acquisition side-effect stays.

---

## 6. Soundness and termination

The coupled map `sol ↦ sol'` where, for each block `P`,
`P.out = denote_defs(P, P.in)` and for each edge `e = (P, c_e) → S`,
`S.in ⊔= refine(P.out, c_e, sol)`, is **monotone**:

- `refine` is monotone in both `P.out` and `sol` (it is a nest of meets/joins
  over abstract states);
- `⊔` is inflationary;
- `widen_join` at WTO heads is inflationary on a bounded lattice.

Kleene iteration with widening therefore **terminates** at a fixpoint. Every
operator is a sound abstract op, so the fixpoint is a **sound
over-approximation**.

**Precision vs the old Phase B.** Inline refinement feeds *tighter* states
into the widen, so the loop head's joined input is no looser than today (the
head is always the full-range join of all its incoming edges regardless), while
body blocks gain precision immediately and the fixpoint **stabilizes in fewer
iterations**. There is **no precision reduction**; there may be a gain (a
refinement can cascade into downstream refinements within the same pass).

---

## 7. Consumer — offset extraction

`Hike_vsa.offsets_of_sub` / `finish`:

- **Delete** the `partitioned_states sub' sol views` call.
- Read each block's **IN-state** from the converged `sol` (the joined refined
  predecessor outputs) and run `denote_def` / `rewrite_addr` / `classify`
  unchanged — they only consume a `Mem.t` / `AI.t` state, which block states
  already are.
- `static_graph_vsa_with_views` returns just `sol`; `offsets_of_sub` drops the
  `views` binding.

---

## 8. Deleted code

- `edge_views_of` (Phase B post-pass driver),
- `partitioned_states` (per-block TAG-state folder),
- the `edge_view` record type (`taken` / `fallthrough` views),
- their callers.

Code comments that cite the deleted machinery's `§`-numbers
(`§1.2`, `§1.4`, `§2.2`, `§2.4`) are now **historical** and must be cleaned
during implementation.

---

## 9. Authoritative vocabulary map (names that actually exist in code)

| Name | Role |
|---|---|
| `operand_constraints` | per-operand backward constraint derivation |
| `def_constraints` | per-def backward constraint derivation |
| `edge_constraints` | pure constraint derivation for **both** True/False sides of a guard |
| `refine_edge` | the complete backward dataflow for one edge (reverse-CFG fixpoint) |
| `reverse_def_walk` | producer subtraction `cstr' = cstr ∩ post(v)` |
| `constrain_cell_on_trace` | trace-exact cell meet (`Mem.meet_range`), cell-gate replacement |
| `decoded_condition` | decodes compound -O0 jcc idioms to guard ops |
| `decoder_constraint` | the nine-row guard→constraint map |
| `complement_guard_op` | complement of a guard op (False-side derivation) |
| ~~`edge_views_of`~~ | **DELETED** |
| ~~`partitioned_states`~~ | **DELETED** |
| ~~`edge_view`~~ | **DELETED** |

---

## 10. Known limitations (recorded, not regressions)

1. **NEQ / non-convex guards** — `comparison_constraint` returns `None` on the
   True side; taken edge identity, fallthrough gets `EQ`. The -O2 `w_big`
   loop-counter class. Inherited from the current code.
2. **Cost** — the deep walk runs on **every forward iteration** (no
   change-driven cache; deliberately accepted). On the small validation corpus
   this is fine; large binaries may be slow. A future change-driven cache
   (re-run an edge's walk only when its source OUT-state changed) would bound
   it without changing precision — left as a follow-up, not required.
