# Verdict: the test-coverage lane (tm/coverage)

Date: 2026-09-11. Worktree `/home/tovpr/hike-cov`, branch `tm/coverage`
(six commits, `bf39a50`..`d0c7d5b`). Baseline: the suite was ALL GREEN
(565 ok checks) with the referee at 2,861,148/0; final: **ALL GREEN at
613 ok checks (+48 pins)**, referee **2,861,148 / 0 mismatches**,
`dune runtest --force` rc=0. NO `dune install`, NO `bap` (the shared
plugin slot untouched). The T13 in-flight files
(`src/cbat_vsa/cbat_walk.ml`, `src/hike_jump.ml`, `test_jump.ml`,
`src/hike.ml`) were not modified.

## The headline: one BUG FINDING (precision class, soundness unaffected)

**The written-slot demotion marks one slot too many.**
`src/hike_vsa.ml`, `callee_side`, the T4b store-demotion rule:

```ocaml
let last = Int64.to_int Int64.(div (add k (of_int (bytes - 1))) 8L) in
```

computes `(k + bytes - 1)/8` — the window base 8 is not subtracted
before the final cell division. The documented rule ("every slot cell
the store's bytes intersect demotes", the T4b ticket's wording) wants
`(k - 8 + bytes - 1)/8`. Measured through the real `offsets_of_sub`
(the coverage lane's new producer pins — the first time this surface
ran at unit level): an 8-byte store at `[RSP+8]` (slot 0, bytes 8..15)
marks slots **0 AND 1**; slot 1's cell `[16,24)` is untouched. The
off-by-one is exactly one slot for EVERY demoting write.

- **Soundness: unaffected.** Over-demotion is the sound direction — the
  demoted slot's reads take the window, which is a superset of the
  parameter (the caller's outgoing stores wrote real window memory).
- **Precision cost:** every window store demotes one extra slot into
  the window-materialization lane instead of a promoted parameter —
  exactly the window-traffic class the program is shrinking (the
  many_args/mixed_fp_int convergence levers).
- **Disposition:** NOT pinned (a pin of the documented rule fails, and
  the suite must stay green; a pin of the current behavior would
  freeze the off-by-one). Reported per the lane contract. The fix is
  the one-line base correction above — the owner decides whether it
  lands now or is inventoried (conversion-first). Re-attribution
  note: T4b's verdict measured demotion working for the
  modify_copy class (the touched slot), which is why this survived.

## The coverage map (module x status)

Status: **PINNED** = unit pins exercise it; **EMISSION-ONLY** = only
the corpus battery / probes touch it; **UNCOVERED** = nothing.

| module / lane | status | evidence |
|---|---|---|
| `src/cbat_vsa` domains (CLP, WordSet, FinSet, word) | PINNED | test_domains (base/policy/agreement/shifts/overlap), D6 width-mismatch rows, test_seed S1-S15 |
| backward refinement (the deep walk, landmarks) | PINNED | test_backward, test_properties (soundness/roundtrip/landmarks/chains), E1/L6/R2 families |
| extraction + kind classification | PINNED (+ this lane) | P21-1, C4a/R11 non-vacuous; **Lane A** now pins the Caller/Range split end-to-end through the real fixpoint |
| VLA detection (`detect_dynamic_alloc`) | PINNED (this lane) | was EMISSION-ONLY (alloca_vla corpus bin only); PR-A5 |
| `Hike_abi` | PINNED (this lane) | was UNCOVERED; PR-E1 (SP-only, RBP ordinary, SysV lanes, unknown-target totality, real-target reified SP) |
| `Hike_kb` (join/order/lookup) | PINNED (this lane) | was UNCOVERED; PR-E2 (extension order, union, the conflict refusal, absence-is-empty) |
| `Hike_stack_model`: regions/split_plan/region_bytes | PINNED | R12-1..9b, C4b; **Lane B** adds the cap's Frame join + diagnostic |
| `Hike_stack_model`: frame geometry (`frame_dims`/`degraded_geometry`/`extent_absurd`, T14) | PINNED (this lane) | was UNCOVERED; PR-B3..B6 (extent sizing, the 64K bounded arm, absurd warn, the 8192 floor + SP-decrement walk) |
| `Sub_layout` / `layout_of_sub` | PINNED (this lane) | PR-B1/B2 (the three arms); the sexp round-trip inside the tag stays UNCOVERED (below) |
| `stamp_def_kinds` / `def_kind` | PINNED | the T10 stamp pin + PR-A5's VLA-marker round-trip |
| `Hike_stack_to_locals` | PINNED (deepened) | was slot-mask only (C1/A4a-c); **Lane C** adds both fission address shapes, the nested-load rewrite, the entry zero-init, the LOW splice, write-closed, ABI-visible (PR-C1/C1b/C2/C3) |
| `Hike_vsa` `callee_side`/`caller_side` (the promotion facts) | PINNED (this lane) | was UNCOVERED at unit level (emission + probes only); PR-A1/A2/A4/A6/A8 (off-by-one finding above) |
| `promote_sub` (the T10 BIR rewrite) | PINNED | T10-PROMOTE/T10-SITE (pre-existing) |
| `resolve_target` | PINNED | T4-RES (pre-existing); the caller-side plumbing pins the None arm (PR-A6) |
| `Hike.Dce` (load-roots, epilogue, sweep) | PINNED | D0-D5 |
| emitter: FP table, poison/Dead/undef warns, sp_restore, casts, golden region GEP, thunks/pointer call | PINNED | test_bil2llvm families 1-9 |
| emitter: VLA lane, SP Slot/anchor per storage class, frame clamp | PINNED (this lane) | was EMISSION-ONLY; PR-D1/D2/D2b/D2c/D3 |
| `Hike_diag` channel (warn contracts) | PINNED | FP-table/unmapped, Unbounded, Dead, undef-read (pre-existing) + absurd-frame, region-cap, frame-clamp (this lane); every contract asserts the load-bearing `hike: ` prefix via captured stderr |
| `bil2llvm_section` `copy_reloc_slots` | PINNED | run_copy_reloc |
| `bil2llvm_section` Project functions (section data, Ogre regions, copy-reloc collection) | EMISSION-ONLY (proposed) | need an in-process `Project.t` fixture; the T6 initializer rendering likewise (fptr_table is its corpus pin) |
| `hike_filter` (`should_filter`, `simplify_jmps`) | EMISSION-ONLY (proposed) | not on the `hike.mli` surface; pinning wants an export (the `copy_reloc_slots` precedent) — `simplify_jmps` is pure-in-sub and exportable cheaply; `filter_subs` needs a Project |
| `hike.ml` (pass pipeline, deps, registration) | EMISSION-ONLY (proposed) | needs `bap` to run; **also T13's wire-up is in flight on another branch** — do not pin now |
| `Hike.Jump` | PINNED | test_jump (T13's file, untouched per the lane contract) |
| Word domain StackOff/band | PINNED (parts) | the seeding/access pins (anchored fixtures, P21-1, E2eC shifts, C3/C4b) exercise propagation through behavior; dedicated band-arithmetic unit pins are thin — noted, not a lane this session |

## The pins (48, committed per lane, all green)

- **Lane A — the producer record** (`offsets_of_sub` end-to-end through
  the REAL fixpoint; the entry seeds RSP at the segment base, the
  production universe): PR-A1 (the `[RSP+8]` read tags `Caller(8,8)`
  and promotes to slot 0, arity 1), A2 (the retaddr cell), A4 (the
  window store + the touched slot's demotion, T4b), A5 (VLA detection:
  the non-literal decrement and not the literal; the VLA kind rides
  the def's value through the stamp), A6 (site slots, SysV indexed,
  last-wins; the unresolvable indirect records None), A8 (the T14
  escape-extent rule: the SP-formed value records `(-16,-16)`; the
  in-band plain integer — the spill_many class, `2^62+5` — records
  NOTHING), A9 (the indirect jump degrades, no refusal), A10 (the
  below-entry store tags `Range(-16,-16)`).
- **Lane B — the frame geometry** (through `layout_of_sub` +
  captured stderr): B1 (precise regions, no frame), B2 (storage-free),
  B3 (extents size the frame: `Range(-32,-8)` -> 48), B4 (Unbounded ->
  the 65552 bounded arm), B5/B5b (absurd band hull + wrapped span warn
  and take the bounded arm — the spill_many/T14 acceptance, unit-pinned
  for the first time), B6 (the degraded walk: the 8192 floor, a
  `0x4000` decrement sizes 16400), B7 (the split-plan cap names itself
  and leaves the plan).
- **Lane C — the stack-to-locals rewrite** (Kb.provide-driven, the
  fixtures state untagged subs by absence): C1 (the COMPOUND-address
  fission shape — the mem operand names the region, the SP index
  arithmetic KEPT: it materializes through the anchor at emission;
  the nested load fissions too), C1b (the BARE-VAR-address shape: the
  temp is replaced by `stack_rN_base` — both operands name the
  region), C2 (the slot zero-init at entry; the narrow-read LOW
  splice), C3 (the ABI-visible exception), + the write-closed control.
- **Lane D — the emitter alloca shapes** (via `emit_program`): D1 (the
  VLA def emits a real runtime-sized `alloca i8` and the model SP
  binds to `vla_i64`), D2/D2b/D2c (the SP Slot per storage class:
  frame anchor GEP, region-0 ptrtoint, storage-free absence),
  D3 (the over-bound frame request warns and clamps — the
  silent-truncation lesson, now loud AND pinned).
- **Lane E — the register facts and the KB domain**: E1 (SP-only stack
  semantics; RBP an ordinary callee-saved GPR; the SysV lanes; the
  unknown-target totality; the real target reifies RSP), E2 (the
  vsa-info order is extension; the join unions disjoint maps and takes
  the bigger of a subset; differing infos for one sub CONFLICT — never
  silently dropped; `info_of_sub` absence = the empty record).

## Findings and shape discoveries worth the record

1. **The written-slot off-by-one** — the headline finding above.
2. **`sp_extents` records one entry per block end** (the same escape
   noted at the body and the exit block). Benign: consumers read
   emptiness and min/max folds. Pinned semantically (membership +
   band-freedom), not the exact list shape.
3. **The fission rewrite's two address shapes are now pinned as they
   are**: `fission_addr`'s `Exp.mapper` override returns `e` for
   non-matching nodes WITHOUT recursing, so the `stack_rN_base`
   replacement fires only for bare-var addresses; compound addresses
   (`RSP - k`, the lifted -O0 shape) keep the SP arithmetic and
   materialize through the SP-Slot anchor (= region-0 for precise
   subs) at emission. Correct end-to-end (37/37 + check_allocas), but
   CONTEXT.md's "Region Base" entry reads as if the base replacement
   were general; the pin now states both shapes explicitly.
4. **A self-check that caught the test, not the code**: my first
   "disjoint map" fixture reused the key — `map_join` correctly
   reported NC->conflict. The pin was split; the code was right.

## Proposed, not implemented (with reasons)

- **`hike_filter` pins** (`should_filter`'s named-exclusion/stub/
  extern/symtab decision; `simplify_jmps`' multi-jmp block split):
  needs a production-surface export (the `copy_reloc_slots` precedent
  makes it legitimate); `filter_subs` additionally needs an
  in-process `Project.t`. NOT done: an export is a src change with an
  owner-review dimension, and this lane's budget went to the
  producer/emitter surfaces above. Cheap follow-up.
- **`hike_sections`' Project functions + the T6 initializer
  rendering**: needs a Project/specification fixture (Ogre). The T6
  rule's acceptance is currently the corpus's fptr_table class only.
- **The pipeline order/deps (`hike.ml`)**: needs `bap`; **and T13's
  wire-up is in flight on those files** — pinning the registration
  now would collide with that agent.
- **`Sub_layout`'s sexp round-trip** (`Stringable`): the tag and the
  module are not on the mli surface; the round-trip is exercised only
  through KB/attr serialization in real runs. Cheap if `Sub_layout`
  is ever exported.
- **KB Toplevel `provide`-conflict behavior** (two differing infos
  provided at the Toplevel): global-state interaction; the pure join
  is pinned (PR-E2) and the Toplevel path is the pipeline's concern.
- **Dedicated band-arithmetic unit pins for the Word domain**
  (StackOff +/min Band-edge propagation): the behavior is exercised
  through every anchored fixture, but no pin names the band edges.
  Candidate for a T15-adjacent lane (the pins re-derive with T15's
  absolute-denotation tags anyway).
