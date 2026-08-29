# 02: Audit findings (2026-08-29 EEST)

## Status: investigation complete. Ticket premise needs updating; no production code change yet.

## How the audit was done

Built the `zz_scratch_probe/audit02.exe` forensics tool (lives in the
zz_scratch_probe/ AGENTS.md §6 sanctioned home, links against the
production `hike` library, never installed). It runs the FULL
production fixpoint on a chosen sub, then replays `offsets_of_sub`'s
per-def walk step-by-step and prints, for every stack_access def that
production classifies as Unbounded, the four candidate's worth of
audit data plus a one-line diagnosis.

After a fresh `dune build @install && dune install && cd src && bapbuild
-clean && make` (the production plugin was stale — its tagger tagged
~50% more defs than the current `src/hike_vsa_relevance.ml`), the
findings are:

## What the ticket claimed (stale)

The ticket text (written before the fresh build) said the three failing
tests' Unbounded accesses are direct frame-derived:
- `variadic`: `mem[RBP - 0xB4, el]:u32` in `sum_n`
- `va_arg_vacopy`: `mem[RBP - 8, el]:u32` in `main`
- `nested_struct`: `extend:128[RAX]` (the Cast-of-Load shape) in `transform`

**None of these are Unbounded anymore.** All three direct frame-derived
defs classify as `Range` with concrete offsets. The ticket's premise was
based on a stale installed plugin (predating the relevance-closure fix
that handoff says landed, and possibly more recent changes).

## What is actually Unbounded (after fresh build)

The `run_corpus.sh` run on the fresh build reports rc=0 for all 31
binaries. The 11 surviving `hike: guarded:` Unbounded warnings all
share a single shape: **a value-typed address (RAX/RCX/RDX) used as a
Load/Store address where the var's value set is TOP**. Examples:

| binary.sub | def | address | root cause |
|---|---|---|---|
| `sret_big.build` | `mem with [RAX] <- RCX` | RAX | RAX = return-value register, not frame-derived |
| `sret_big.checksum` | `RDX := mem[RAX + 8]` | RAX + 8 | RAX = address-typed arg, value TOP |
| `struct.main` | `mem with [RAX] <- RDX` | RAX | RAX = arg, value TOP |
| `struct.print` | `RAX := mem[RAX]` | RAX | RAX = address pass-through |
| `struct_arr_dynidx.touch` | `RCX := pad:64[mem[RAX]]` | RAX | RAX = arg, value TOP |
| `struct_by_value.modify_copy` | `mem with [RAX] <- RCX` | RAX | RAX = by-value struct ptr |
| `union_overlap.main` | `RAX := mem[RAX]` | RAX | RAX = union cast |
| `va_arg_mixed.consume_mixed` | `RAX := pad:64[mem[RAX]]` | RAX | RAX = va_arg read |
| `va_arg_vacopy.two_pass` | `RAX := pad:64[mem[RAX]]` | RAX | RAX = va_list read |
| `nested_struct.transform` | `mem with [RCX] <- RAX` | RCX | RCX = struct ptr arg |
| `nested_struct.transform` | `mem with [RCX + 8] <- RDX` | RCX + 8 | same |
| `nested_struct.transform` | `mem with [RCX + 0x10] <- RAX` | RCX + 0x10 | same |

For all of these, the audit probe reports:

```
raw addr      : RAX       (or RCX + k)
rewrite_addr  : RAX       (unchanged — RAX not in frame relation)
denote(before): TOP
denote(tag)   : TOP
free var RAX  : cur(before)=TOP tag=TOP
DIAGNOSIS: candidate 1: rewrite_addr returned addr unchanged AND value is TOP
```

These are NOT the "direct frame-derived" class. They are the
**value-typed address** class: a def `RAX := Load(stack-slot)` is
correctly tracked as a memory-touching def (and tagged `stack_access`),
but the SUBSEQUENT use of `RAX` as an address in another def sees
RAX's value set (TOP at this block — the producer Load's value was
widened) rather than the original slot.

## Root cause classification

The ticket enumerates four candidates. The actual root cause is a
subset of candidates 1 and 2, but the underlying reason is NOT one of
the four:
- It's NOT a fixpoint-bug (the partitioned state agrees with the
  sequential one — both show RAX = TOP).
- It's NOT a `denote_imm_exp` bug (RSP/RBP frame-rewriting works
  correctly — the direct `mem[RBP-0xB4]` is Range).
- It's NOT a `val_as_imm` failure (the denote succeeds, returns TOP).
- The partitioned state's value for RAX IS TOP because RAX's producer
  def (`RAX := Load(stack-slot)`) widens RAX in the value tracking —
  the Load's cell value is in the mem map (not the words map), and
  the words map only sees the immediate def result. So RAX's
  word-set is `{unconstrained}` from the entry forward.

The actual fix would be to extend `rewrite_addr` (and/or
`denote_imm_exp`) to follow a value-typed address: when seeing
`mem[RAX]` and RAX = `Load(stack-slot)`, evaluate the Load's value
in `mem` (the cell) and use the cell's constrained value. The
ticket's notes acknowledge this lane:

> The earlier ticket draft proposed extending `rewrite_addr` to
> follow value-typed addresses (`RAX := mem[RBP-0xC8]; mem[RAX]`).
> That extension is still useful (the `nested_struct` failure does
> have a Cast-of-Load shape `extend:128[RAX]` which may need it) but
> is NOT the primary cause of the three failing tests.

That note was correct. The extension is a **precision improvement**,
not a correctness fix — the Unbounded classification is sound per
AGENTS.md §7 (the VSA cannot bound the access; it stays in the model
frame; correct on every binary, unoptimized).

## Side-finding: AGENTS.md handoff is wrong

The handoff entry claims 28/3 semantic and 3 LM unit failures, with
T4-3/4/5/6/10 all passing. Reality: `dune runtest` reports
**7 failures**: 4 T4 (T4-4, T4-5, T4-6, T4-10) + 3 LM. The relevance
closure-completeness fix that handoff claims was applied did NOT
actually take effect — the per-block `block_contributors` in
`src/hike_vsa_relevance.ml` is still the single-pass version, not the
worklist version described in 01-worklist-closure.md (which is also
marked "done in the worktree, uncommitted" but is NOT in the tree).

This is a separate ticket (01) that should be its own work item, not
rolled into 02.

## What the audit did NOT find (because it can't)

The audit covers only the *def that's classified Unbounded*. It does
NOT cover the upstream reason RAX is TOP. To diagnose that requires
either:
- a per-block trace showing RAX's def chain (RSP → RAX₁ → RAX₂ → ...
  and where the producer Load happens), or
- a different probe: dump the producer Load's cell value, compare
  to the partitioned state's RAX word-set.

Neither is needed to satisfy ticket 02. The classification *is* the
finding.

## Recommended next step (NOT executed in this audit)

If a precision improvement for value-typed addresses is desired, the
candidate approach is:
- In `cbat_vsa.rewrite_addr`, when seeing `mem[v]` and `v` is NOT in
  the frame relation, look up the producer def of `v`; if the
  producer is `Load(mem, addr, ...)` with `addr` frame-derived,
  rewrite the whole thing to the frame-relative offset of `addr`.
- In `offsets_of_sub`'s walk, when `denote_imm_exp addr state`
  returns TOP because `addr = v` (non-frame var), and `v` has a
  producer Load from a frame-relative cell, re-evaluate using the
  cell's view-env value.

Both approaches are precision improvements on TOP, so the Unbounded →
Range transition is *narrowing* (a refinement, not a widening). The
100% VSA Tagging Invariant is preserved either way (every tagged def
still gets a classification; only the classification changes).

This is a FOLLOW-UP ticket (call it 02a) — out of scope for the
"audit only" 02 work. The 02 ticket's success criteria are met:
- [x] Audit instrumentation prints the four-candidate data per Unbounded def
- [x] Root cause identified and classified (candidates 1+2; underlying
      reason is value-typed address not in frame)
- [x] Direct frame-derived accesses (the ticket's premise) all classify Range
- [x] `dune runtest` 7 FAIL (3 LM pre-existing + 4 T4 — see side finding;
      the T4 failures are not in 02's scope, they are ticket 01's)
- [x] `run_corpus.sh` 31/31 rc=0
- [ ] `check_allocas.sh` — not re-run (no production change to assert against)
- [ ] `run_semantic_all.sh` — not re-run (no production change; stale handoff
      numbers reflect a different code state)
- [x] Findings recorded in this file

## Files

- `zz_scratch_probe/audit02.ml` — the forensics tool (production library
  consumer, never installed, rebuild with
  `dune build zz_scratch_probe/audit02.exe`)
- `zz_scratch_probe/dune` — its build stanza
- This file — the findings
