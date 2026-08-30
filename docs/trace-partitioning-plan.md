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
2. In `denote_jump`, the transfer is driven by the **BAP IR graph**:
   - compute `g = Sub.to_cfg sub` ONCE at fixpoint entry (free projection);
   - for each out-edge `e` of the current block: derive seeds from the
     **accumulated** `Graphs.Ir.Edge.cond e g` (NOT the jmp's own cond),
     run the deep backward walk, join into `Dst(e).in`;
   - the uniform rule covers conditional, unconditional, and chain-tail
     edges (a lone goto's cond is `1` = identity).

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

**NEQ guards (re-verified 2026-08-30):** a *decoded* `jne` guard (`~ZF` →
NEQ) refines the **taken** edge exactly — `decoder_constraint`'s NEQ row is
the two-piece `TOP − {c}` with the exclusion of `c` at the meet — and `jz`
(`ZF` → EQ) pins the taken edge to `{c}`; the fallthrough gets the complement
via `complement_guard_op`. The `None` sound-stop survives only for
**non-decoded** NEQ comparison guards (`comparison_constraint`'s `Bil.NEQ`
row, the non-convex two-sided class): there the taken edge is identity and
the fallthrough gets `EQ`. The decoded rows are part of the
landmark-consumption work whose strict F1-NEQ acceptance test (head max = K
exactly) is green on the current tree; §5 preserves that chain.

### Condition chains — the accumulated path condition (user directive, 2026-08-30; BAP-native, tested)

In BAP the gotos are like `when c1 goto l1; when c2 goto l2; goto l3` —
**multiple jmp terms in ONE block**, first-true-wins (switch semantics).
**For a cond in a chain, every previous cond that was not true must be used
to refine** — when the last cond is TRUE, the previous negative conds are
used. Verified by probe (2026-08-30, `Graphs.Ir.Edge.cond` on a KBIL
fixture): **BAP's IR-graph API accumulates the conds NATIVELY** —

```
edge chain→l2:  own = c2                     acc = c2 & ~c1
edge chain→l3:  own = 1  (unconditional)      acc = ~c1 & ~c2
```

`Sub.to_cfg sub : Graphs.Ir.t` is a free projection of the same sub, and
`Graphs.Ir.Edge.cond : edge -> graph -> exp` computes the **accumulated path
condition** per edge ("takes into account all conditions preceding the
edge") — including on the trailing unconditional goto. The design therefore
needs NO chain-specific machinery:

1. **THE UNIFORM TRANSFER RULE:** every out-edge `e` of block `B` transfers
   `deep_refine(B.out, Edge.cond e g, sol)` into `Dst(e).in` — conditional,
   unconditional, and chain-tail edges alike. A lone `goto` has cond `1`
   (identity). The taken/fallthrough two-refinement falls out: for
   `when c goto A; goto B`, edge→A carries `c`, edge→B carries `~c` —
   computed by BAP, not by us. **Invariant: no out-edge may skip its
   refinement** — skipping a chain carrier silently drops its negative for
   every downstream cond.
2. **Inter-block chains** (else-if ladders, one hop per block) accumulate
   NATURALLY through the state flow: each hop's fallthrough edge is refined
   by its own (Edge-computed) negation, so the state arriving at the next
   hop already carries the previous negatives; the last cond's refinement
   applies to the accumulated state. No explicit walk-back.
3. **THE ONE NEW RULE** (`edge_constraints` extension): `Edge.cond` emits
   *syntactic* forms — `~(x op c)` and `&`-conjunctions. Required arms:
   - **NOT-unwrap**: `~(x op c)` → the complement row (`NEQ→EQ`, `EQ→NEQ`,
     `LT→GE`, `LE→GT`, `SLT→SGE`, `SLE→SGT` — `complement_guard_op` has the
     guard_op rows already);
   - **AND-conjoin**: each conjunct independently seeds constraint derivation
     over the same env (intersection).
   Everything else consumes the accumulated cond through the existing seed
   machinery unchanged.
4. **Precompute once:** the accumulated conds are STATIC per sub (they do
   not depend on the solution) — compute `Sub.to_cfg` and every edge's
   `Edge.cond` once at fixpoint entry, cache per (block, edge), never
   re-derive per iteration.

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
  is **KEPT, not replaced** — the deep walk is added on top of it. The shallow
  step (guard-var meet + the `constrain_def_chain` walk whose MINUS row lets a
  jne-guarded counter stabilize AT the landmark — the green F1-NEQ chain) is
  cheap; both paths share `constrain_def_chain`, but end-to-end equivalence of
  the deep walk alone is unverified, so the pre-step stays. Landmark
  acquisition (`observe_unsat_var` inside the meets) fires from both paths.

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
- the `_with_views` wrapper,
- their callers.

Code comments that cite the deleted machinery's `§`-numbers
(`§1.2`, `§1.4`, `§2.2`, `§2.4`) are now **historical** and must be cleaned
during implementation.

**Blast radius beyond `src/` (verified 2026-08-30):** the deleted names are
public API and test fixtures, not just dead production code —

- `cbat_vsa.mli` exposes `edge_view`, `edge_views_of`, `partitioned_states`,
  and the wrapper; the `.mli` entries go with the bodies. After any
  `cbat_vsa*.mli` change the corpus re-emission must run
  `cd src && bapbuild -clean && make` (the stale-interface gotcha).
- The unit suite calls the wrapper at several fixtures and builds views via
  `edge_views_of` (the view-lookup helpers); the R6/G3 tests assert **per-edge
  view** properties (taken = the `TOP−{c}` arc, fallthrough = `{c}` exactly).
  Deleting Phase B means MIGRATING these tests to the inline-refined
  IN-states — and a multi-predecessor block's IN-state is the JOIN of its
  incoming refined edges, so a per-edge assertion stays faithful only on
  single-predecessor destinations.
- The precision probe computes exactness from the wrapper +
  `partitioned_states`; it migrates to IN-state reads. The corpus watcher is
  already on the solution-only engine — unaffected.

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
| `complement_guard_op` | complement of a guard op (the NOT-unwrap rows for `Edge.cond`'s syntactic `~(x op c)`) |
| `Graphs.Ir.Edge.cond` | **BAP-native accumulated path condition** per edge (`Sub.to_cfg`) — includes the preceding when-chain negatives; the fused transfer's input |
| ~~`edge_views_of`~~ | **DELETED** |
| ~~`partitioned_states`~~ | **DELETED** |
| ~~`edge_view`~~ | **DELETED** |

---

## 10. Known limitations (recorded, not regressions)

1. **NEQ, non-decoded** — for guards the jcc decoder does not recognize,
   `comparison_constraint`'s `Bil.NEQ` row returns `None`; taken edge
   identity, fallthrough gets `EQ`. (Decoded `jne`/`jz` guards refine exactly
   — see §4.) The -O2 `w_big` residual class. Inherited.
2. **Per-edge views collapse at joins** — the fused design refines the JOINED
   destination IN-state; a multi-predecessor block loses the per-edge
   partition (a loop head is the join of the entry-refined and
   back-edge-refined states). Fine for offset extraction; per-edge view
   assertions in tests must pick single-predecessor targets.
3. **Cost** — the deep walk runs on **every forward iteration** (no
   change-driven cache; deliberately accepted). On the small validation corpus
   this is fine; large binaries may be slow. A future change-driven cache
   (re-run an edge's walk only when its source OUT-state changed) would bound
   it without changing precision — left as a follow-up, not required.
