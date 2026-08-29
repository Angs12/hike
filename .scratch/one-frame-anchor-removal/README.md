# One-Frame Anchor Removal — triage overview

**Date:** 2026-08-29
**Tree:** `feature/100-percent-vsa-tagging` (1340124 + uncommitted relevance-cleanup-02 + worklist closure fix)
**Goal:** Recover the 3 surviving corpus failures (`out_nested_struct`,
`out_va_arg_vacopy`, `out_variadic`) by re-architecting the VSA + relevance
+ emitter around a single one-frame model with no anchor offset arithmetic.

## Architecture (the agreed design)

- **One large alloca per sub** (the frame). No per-region split.
- **No anchor offset arithmetic** — the frame base IS the entry RSP.
- **VSA subsumes the relevance pass** — the AI state carries `sp_derived_vars`
  as part of the lattice; a single pass does both the value-tracking and
  the sp-derivation propagation. The relevance pass shrinks to tag
  application + the 100% VSA Tagging Invariant assertion.
- **VSA value-tracking extension** — `rewrite_addr` looks up register
  values, follows pointer derefs, applies the frame relation recursively.
  The value-typed-address class (`RAX := mem[RBP-0xC8]; mem[RAX] := ...`)
  resolves to a concrete offset.
- **Per-call alloca for va_list / struct-by-value args** — the caller
  allocates a fresh alloca for the call's data, passes its address as
  the `hike_stack` arg. The callee reads/writes via a stable pointer,
  no inttoptr arithmetic with anchor-relative offsets.
- **Worklist on the VSA-tracked closure** — the backward closure is a
  single pass through the VSA's `sp_derived_vars` set, not a separate
  syntactic analysis.

## Failure → fix mapping

| Failure | Root cause | Fix ticket |
|---|---|---|
| `out_nested_struct` (by-value struct copy/return) | Per-region alloca split breaks contiguous struct layout | T05 (drop the anchor; one flat frame, no per-region split) |
| `out_va_arg_vacopy` (vacopy + va_list) | Vacopy address is a register-var, not literal RSP; per-region alloca picks wrong region | T03 (per-call alloca for va_list/struct) + T05 |
| `out_variadic` (va_arg iteration) | Value-typed-address (`RAX := mem[...]; mem[RAX] := ...`) not resolved by VSA | T02 (VSA value-tracking) |

## Triage order

1. **T01 (worklist closure)** — DONE. Pure refactor of `block_contributors`,
   recovers T4 unit tests, no semantic gate impact. In the worktree,
   uncommitted.
2. **T02 (VSA value-tracking)** — `rewrite_addr` looks up register values.
   ~80 LOC, additive. Targets `out_variadic`. Land first; re-run gates.
3. **T03 (per-call alloca for va_list/struct)** — caller-side alloca
   routing. ~120 LOC. Targets `out_va_arg_vacopy` and `out_variadic`
   (struct-by-value class).
4. **T04 (VSA subsumes relevance)** — wide refactor. `cbat_ai_representation.ml`
   adds `sp_derived_vars` to the AI state; `hike_vsa_relevance.ml` shrinks
   to ~100 LOC. Expand–contract sequence: add the new form beside the old,
   migrate, contract.
5. **T05 (drop the anchor)** — wide refactor. `bil2llvm.ml` switches
   from the per-region `stack_rN` allocas + anchor offsets to one flat
   frame alloca. Expand–contract: keep the old `build_frame_anchor` and
   `region_split_plan` alongside, add a `build_flat_frame` lane, route
   `create_sub` through it, retire the old.

## Validation gate per ticket

- `dune runtest` — unit tests, including the 12 T4 checks and the 3 LM
  failures (pre-existing, expected to remain failing).
- `bash scripts/run_corpus.sh /tmp/corpus /tmp/heritage_<tag>` — 31/31
  rc=0.
- `bash scripts/check_allocas.sh /tmp/heritage_<tag>` — 124/0.
- `bash scripts/semantic/run_semantic.sh /tmp/corpus /tmp/heritage_<tag> /tmp/sem_<tag>` — 8/8.
- `bash scripts/semantic/run_semantic_all.sh /tmp/corpus /tmp/heritage_<tag> /tmp/sem_all_<tag>` — progress 28/31 → 29/31 → 30/31 → 31/31.

The 3 LM F1/F2c unit failures are unrelated to this work (landmark-
directed widening, pre-existing) and remain failing throughout.

## Reference

- `.scratch/redesign-sketches.md` — the 5-skeleton design.
- `AGENTS.md` §Current validation state — the gates and the 3 failures.
- `docs/trace-partitioning-plan.md` — the relevance architecture that
  is being subsumed.
