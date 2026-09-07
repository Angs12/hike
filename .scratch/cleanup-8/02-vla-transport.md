# Ticket 02 — VLA transport: one fact, one producer

Status: landed (2026-09-06).

## Problem

`Cbat_vsa.Cbat_extraction.detect_dynamic_alloc` (a `Var.Map` fold + a full
`Term.visitor` over the sub — `cbat_vsa.ml:3096-3133`) runs **three times per
sub**:

| site | file:line | gating |
|---|---|---|
| producer | `hike_vsa.ml:34` | unconditional (the natural owner) |
| stack model | `hike_stack_model.ml:586` (`has_vla_dynamic_alloc`) | gated by `convertible <> []` (206/707 subs on ls) |
| emitter | `bil2llvm.ml:1771` | unconditional, on the **post-stl/post-dce sub** |

Measured: 0.065-0.100 s/binary across all three sites (f8census, ls/du).
Additionally the `vla_bounds` fold (`cbat_vsa.ml:3038-3060`) walks the whole
sub and discards everything when `alloc_tids` is empty — which is 706/707
subs on ls, 761/761 on du.

## Change

1. **Transport**: add `vla_alloc_tids : Tid.Set.t` to `Convutils.vsa_info`
   (`convutils.ml:88-96` — the record already carries `vla_bounds`, the
   per-VLA size bounds; this carries the *detection* result). Producer fills
   it at `hike_vsa.ml:34`; `mk_vsa_info`/`mk_vsa_info_maps` grow the field
   (`convutils.ml:115-131`); `equal_vsa_info` grows
   `Core.Set.equal Tid.set_equal i1.vla_alloc_tids i2.vla_alloc_tids`
   (settled fallback if a gate moves: don't compare the field — transport
   semantics only; decide during implementation, don't pre-commit).
2. **Consumers read it**: `bil2llvm.ml:1771` reads
   `sub_info.vla_alloc_tids` (the `sub_info` is already in scope at :1768);
   `hike_stack_model.ml:586` reads `info.vla_alloc_tids` (the info is a
   parameter of `split_plan`).
3. **Guard**: the `vla_bounds` fold at `cbat_vsa.ml:3038` —
   `if Core.Set.is_empty alloc_tids then Tid.Map.empty else <fold>` (same
   edit-site neighborhood; one line).

## The one soundness check (do this FIRST, before any edit)

The emitter's detection runs on the **post-rewrite sub**; the transported set
was computed on the **pre-rewrite sub**. The sets are equal iff stl+dce never
remove a Dynamic Allocation def (an SP-decrement-by-runtime-size def, or its
`tmp := RSP - size` producer — `vla_decrement_p`, `cbat_vsa.ml:3065`).

- stl rewrites only memory-access cells (`stack_to_locals`); it cannot remove
  an SP-decrement def. Safe by construction.
- dce: the **precise** path erases `is_sp_for_erasure`/`is_sp_value_def`
  defs — `RSP := RSP - size` IS `is_sp_for_erasure` (lhs = SP) and IS
  `is_sp_value_def` (rhs reads SP), so the precise path erases exactly the
  epilogue-adjacent pushes while the real VLA decrement... **must survive
  because RSP is used downstream** (every subsequent mem access / the ret
  epilogue reads it — `Jmp.free_vars` of indirect jumps and rets include
  RSP). VERIFY this concretely: on a VLA corpus binary (`alloca_vla`),
  confirm the emitted module still contains the dynamic alloca after dce
  (it does today — the corpus is green — but confirm the *tid set* the
  emitter sees is identical pre/post dce with a one-off debug print under
  `#ifdef VSA_DEBUG`). If they differ, the emitter keeps its own detection
  and only the stack-model site reads the transport (still kills 1 of 3).

## Verification

- Full battery + IR byte-identity 35/35 (the record-shape change is the
  only semantic-adjacent risk; identical IR ⇒ identical everything).
- `dune runtest`: the A4 fixture borrows C1's `vsa_info` — the field gains a
  default at every `mk_vsa_info` call site (fixtures pass `Tid.Set.empty`
  unless they mean otherwise).
- `alloca_vla` probe (`precision_probe`) still passes — the VLA path's
  end-to-end oracle.
