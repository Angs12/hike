# Redesign Sketches — Anchor Removal & One-Frame Model

**Date**: 2026-08-29
**Status**: Pre-ADR. Pending approval.

The 5 changes in the agreed redesign. Each sketch is **pseudocode / structural** — actual OCaml types and signatures are the design; the body is illustrative.

The architecture after this redesign:

- **One alloca per sub** = the frame. No per-region split. No anchor (frame base = entry RSP).
- **VSA fixpoint** carries `(sp_derived_vars, AI_state)` as the lattice. Single source of truth for "is this def sp-derived?" — replaces the relevance pass's forward-var-set.
- **Relevance pass** is subsumed into the VSA. `hike_vsa_relevance.ml` shrinks to ~100 LOC (just tag application + the 100% VSA Tagging Invariant assertion).
- **Weak lattice** for untagged defs: a cheap "don't care" value that doesn't add fixpoint cost.
- **Three passes**: relevance (folded into VSA), offset (VSA classification), live-range (region merge — but now with the one-frame model, this is just the VSA's offset tags).

---

## Sketch 1: VSA lattice subsumes relevance — `(sp_derived_vars, AI_state)` pair

**File**: `src/cbat_vsa/cbat_ai_representation.ml` (the AI state type) and `src/cbat_vsa/cbat_vsa.ml` (the transfer function).

### Current shape

```ocaml
(* The AI state is just an abstract state — words, memory, frame.
   The relevance pass is a SEPARATE analysis that produces a set of
   sp-derived tids, used as a filter by [denote_def]. *)
type ai_state = { words : ...; memory : ...; frame : ... }
val denote_def : def term -> ai_state -> ai_state
```

### New shape

```ocaml
(* The AI state now carries BOTH the abstract state AND the
   sp_derived_vars set. The transfer function updates both in one
   pass — the relevance analysis IS the value-tracking, and the
   "is this def sp-derived?" question is answered by the frame
   relation, not by a separate syntactic pass. *)
type ai_state = {
  words : ...;
  memory : ...;
  frame : ...;
  sp_derived_vars : Var.Set.t;  (* NEW: the relevance closure (forward) *)
}

(* Updated transfer function: *)
val denote_def : def term -> ai_state -> ai_state
(*   - For an untagged def (e.g. a pure register arithmetic that doesn't
     touch RSP/RBP/memory), the AI state is updated but
     sp_derived_vars is unchanged. The value-tracking computes a Weak
     word (don't care) cheaply.
   - For a tagged def (Load/Store with sp-derived address), the AI
     state is updated AND the def's LHS is added to sp_derived_vars
     (the forward propagation). The value-tracking computes a
     concrete word. *)
```

**Key change**: the VSA's `denote_def` is the ONLY pass that processes defs. The relevance pass's `forward_vars` and `backward_slice` are GONE. The `hike_vsa_relevance.ml` becomes:

```ocaml
(* Just the tag-application post-pass + the 100% VSA Tagging Invariant.
   The VSA's output already includes per-def classifications; this pass
   just applies the `relevant`, `stack_access`, `dynamic_alloc` tags
   based on the VSA's results. *)

val analyze : var -> sub term -> sub term
(* For each def:
   - if VSA's classification is Some(kind) and is_stack_access_shape(def):
     tag with `stack_access` AND `relevant`
   - if the def is in the VSA's `relevant` set (any def whose value
     flows into a stack-access address): tag with `relevant`
   - if `detect_dynamic_alloc(def)`: tag with `dynamic_alloc` *)
```

### The Weak lattice for untagged words

```ocaml
(* A "Weak" word represents "we don't care about this value".
   Lattice-wise: Weak ⊥ Weak (i.e., Weak is bottom — joining with Weak
   is a no-op). Computing with Weak is O(1). *)
type word =
  | Strong of WordSet.t
  | Weak

(* The frame-relation propagation: a def is sp-derived if its
   address expression contains a frame-derived register. This is
   a property of the def's rhs in the current frame state, not
   a separate analysis. *)
val is_sp_derived_def : ai_state -> def term -> bool
(* Returns true if the def is a Load/Store with an sp-derived
   address, OR a non-memory def whose rhs contains a frame-derived
   register (a copy that propagates sp-derivation forward). *)
```

### Dependency

- The AI state type in `cbat_ai_representation.ml` grows by one field (`sp_derived_vars`).
- The `denote_def` function updates `sp_derived_vars` based on `is_sp_derived_def`.
- The `hike_vsa_relevance.ml` shrinks to ~100 LOC (just tag application + invariant assertion).

---

## Sketch 2: VSA value-tracking extension (look up register values, follow pointer derefs)

**File**: `src/cbat_vsa/cbat_vsa.ml` — the `denote_imm_exp` and `rewrite_addr` functions.

### Current shape

```ocaml
val rewrite_addr : frame option -> exp -> exp
(* Only handles DIRECT frame-derived addresses.
   [mem[RAX]] where RAX is a value (not directly frame-derived) gets
   rewritten to the same expression (no change) — the VSA returns
   TOP, the address is classified as Unbounded. *)
```

### New shape

```ocaml
(* VALUE-TYPED ADDRESS RESOLUTION.
   For [mem[REG]] or [Store(mem, REG, v)], if REG's value-set in
   the current state is a SINGLETON {e} where e is a frame-derived
   affine expression, substitute e for REG and recurse. *)
val rewrite_addr : frame option -> ai_state -> exp -> exp
val denote_imm_exp : exp -> ai_state -> ws_result
```

**Algorithm**:

```
rewrite_addr(frame, state, addr):
  match addr:
  case BinOp(PLUS|MINUS, base, const):
    base' = rewrite_addr(frame, state, base)
    return apply_binop(base', const)
  case Var(v):
    match state.find_word(v):
      | Strong(singleton(e)) -> rewrite_addr(frame, state, e)
      | Strong(multi) | Weak  -> addr
  case Cast(typ, _, inner):
    return Cast(typ, _, rewrite_addr(frame, state, inner))
  case Load(mem, inner_addr, ...):
    inner' = rewrite_addr(frame, state, inner_addr)
    return Load(mem, inner', ...)
  case Int(_): return addr
  case _: return addr
```

Termination: depth-bounded (≤ 8) to prevent loops in cyclic value patterns.

---

## Sketch 3: Drop the anchor — frame is a flat slab

**File**: `src/bil2llvm.ml` — `create_sub`, `create_load`, `create_store`, `rebase_addr`, `create_static_mem_access`, `mem_access_via_ptr`.

### Current shape

```ocaml
(* The frame is [N x i8] with anchor at [N-8]. All inttoptr
   arithmetic is computed from anchor_i64. The model is: RSP =
   anchor - 8, RBP = anchor - 8 - 0x1f00, etc. *)
let frame = alloca [N x i8] ... in
let anchor = GEP i8, frame, N-8 in
let anchor_i64 = ptrtoint anchor to i64 in

let create_load addr =
  match classify addr with
  | Range(lo, hi) when lo = hi ->
      GEP i8, frame, (lo - 8)  (* the anchor-relative offset *)
  | _ ->
      inttoptr (add anchor_i64, offset) to ptr
```

### New shape

```ocaml
(* The frame is [N x i8] — a FLAT slab. No anchor. The frame base
   IS the entry RSP. *)
let frame = alloca [N x i8] ... in
let frame_i64 = ptrtoint frame to i64 in
(* No anchor_i64. No anchor GEP. The frame_i64 replaces the
   anchor_i64 in all uses. *)

let create_load addr =
  match classify addr with
  | Range(lo, hi) when lo = hi ->
      GEP i8, frame, lo  (* direct GEP into the flat frame *)
  | _ ->
      inttoptr (add frame_i64, offset) to ptr
```

**Key changes**:
- The `frame` is allocated as a flat slab (no `anchor` field).
- The `frame_i64` IS the entry RSP value (no separate `anchor_i64`).
- The `frame + offset` is a direct GEP for static offsets, or `inttoptr (frame_i64 + e) to ptr` for runtime expressions.
- The `restore_sp_after_call` function (from the L-E1e fix) is UNCHANGED — it rebinds the SP local to `post_push + 8` at the fallthrough block.
- The `is_abi_visible` logic for `lo > 0` (incoming-arg cells) is unchanged — it routes to `inttoptr(stack + lo)`.

### What goes away

- The `build_frame_anchor` function (line 1579-1596) — replaced by a simple `build_frame` that just allocates the flat slab.
- The `degraded_dims` function (line 1598-1652) — replaced by a simple VSA-driven size calculation.
- The `clamp_hi` 0x40000000 cap — replaced by a more principled size policy.
- The per-region alloca split (`stack_rN`) — the `region_split_plan` gate and all its checks are GONE.

---

## Sketch 4: Per-call alloca for va_list / by-value struct args (caller side)

**File**: `src/bil2llvm.ml` — `create_func_call`, `create_call_args`, and a new `create_call_data` function.

### Current shape

```ocaml
(* The caller pushes args onto its stack and passes a hike_stack
   pointer to the callee. The callee reads via inttoptr arithmetic
   with the (now-misaligned) offsets. *)
let create_func_call ... =
  store 60, inttoptr (add rsp, -16) to ptr
  store 70, inttoptr (add rsp, -8) to ptr
  call sum_n(rdi, rsi, ..., hike_stack = rsp)
```

### New shape

```ocaml
(* The caller allocates the call's data layout in a fresh alloca and
   passes the alloca's address as hike_stack. The alloca is a
   stable pointer; the callee reads/writes via it. *)
let create_func_call ... =
  let call_data = alloca [call_data_size x i8] ... in
  let call_data_i64 = ptrtoint call_data to i64 in
  store 60, GEP i8, call_data, 8
  store 70, GEP i8, call_data, 16
  call sum_n(rdi, rsi, ..., hike_stack = call_data_i64)
```

**Key changes**:
- The caller allocates a fresh per-call alloca for the va_list / struct-arg data.
- The alloca is initialized with the actual values.
- The alloca's address is passed as the `hike_stack` argument.
- The callee uses the alloca's address as a stable pointer — NO inttoptr arithmetic with anchor-relative offsets.

### What this changes about the callee side

The callee's va_arg iteration:
- `RAX := mem[hike_stack - 0xC8]` (load the `overflow_arg_area` pointer) — reads from the caller's per-call alloca.
- `RAX := mem[RAX]` (load the va_arg value) — reads from the actual overflow area.
- The va_arg iteration works correctly because the alloca is a single contiguous block.

### Dependency

- The `create_func_call` function needs to know the SIZE of the per-call alloca. This is determined by the callee's `info.Convutils.offsets` (the span of all accesses the callee makes via the `hike_stack` arg) plus the va_list struct layout.
- A new VSA field: `callee_arg_area_size` (per-sub, the max offset the callee reads/writes via hike_stack).

---

## Sketch 5: Closure worklist — VSA-tracked, not syntactic

**File**: `src/hike_vsa_relevance.ml` — gone (folded into VSA per Sketch 1) OR kept as a thin post-pass if the backward closure can't be folded in.

### Current shape

```ocaml
(* The worklist in the new closure fix (sketch 1 of the vsa100 redesign) walks the syntactic def-use closure. *)
```

### New shape

The VSA-tracked closure is the VSA's `sp_derived_vars` set, which is part of the AI state. The closure of a stack access is the transitive closure of `sp_derived_vars` starting from the stack access's def. This is a SINGLE pass through the VSA's output:

```
for each (def, classification) in VSA's output:
  if classification is stack_access_shape:
    add def to tagged_defs (backward closure root)
    for each var in def.rhs (the address):
      for each producer def in VSA's def_of_lhs(var):
        add producer to tagged_defs (BFS)
        recurse on producer's rhs
```

**Termination**: each def is added at most once. Bounded by the total defs in the sub.

**Why this is better than the syntactic closure**:
- The VSA's `sp_derived_vars` set already accounts for value-typed addresses (via the frame-relation propagation).
- The backward closure can also use the VSA's value-tracking: a def whose value is `{RSP - 0xB4}` is sp-derived via the frame-relation, not just via syntactic def-use.
- No separate syntactic analysis — the VSA's output IS the closure.

### Dependency

- The VSA's `sp_derived_vars` set must be exposed in the output (sketch 1).
- The backward-closure walk uses the VSA's `def_of_lhs` (which the VSA already maintains).

---

## Summary of the 5 changes

| # | Change | File(s) | LOC estimate | Risk |
|---|---|---|---|---|
| 1 | VSA lattice subsumes relevance; `Weak` for untagged | `cbat_ai_representation.ml`, `cbat_vsa.ml`, `hike_vsa_relevance.ml` (shrink) | ~200 (VSA growth) −190 (relevance shrink) = ~10 net, but BIG refactor | High (new lattice, breaking API) |
| 2 | VSA value-tracking extension | `cbat_vsa.ml` | ~80 (rewrite_addr + tests) | Medium (new API, depth-bounded recursion) |
| 3 | Drop the anchor | `bil2llvm.ml` | ~80 (build_frame rewrite + create_load/create_store updates) | Medium (sign-flip in offset semantics, restore_sp_after_call re-verify) |
| 4 | Per-call alloca for va_list/struct args | `bil2llvm.ml` | ~120 (create_func_call + new size computation) | Medium-High (size computation, init) |
| 5 | Closure worklist on VSA output | (folded into VSA per Sketch 1; no separate code) | 0 | — |

**Total**: ~210 LOC across 3 files. The `cbat_vsa` change (sketch 1) is the most invasive — it changes a public API and adds a new lattice component.

**Order of implementation**:
1. **Sketch 5 → implemented as worklist in `block_contributors`** (DONE — pure refactor, no new API).
2. **Sketch 2 → VSA value-tracking extension** (look up register values, follow pointer derefs). This is a small additive change.
3. **Sketch 4 → per-call alloca for va_list/struct args** (focused change in `bil2llvm.ml`).
4. **Sketch 1 → VSA lattice subsumes relevance** (the big refactor — AI state carries `sp_derived_vars`, `hike_vsa_relevance.ml` shrinks).
5. **Sketch 3 → drop the anchor** (depends on sketches 1, 2, 4 being correct; final cleanup).

**Validation**: same gates as before (`dune runtest`, `run_corpus.sh`, `check_allocas.sh`, `run_semantic.sh` 8-bin, `run_semantic_all.sh` 31-bin). The 3 remaining failures should pass; the 28 currently-passing should remain passing; the LM F1/F2c tests (3 pre-existing) are unrelated and remain failing.
