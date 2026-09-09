# 04 — generalization: the typed frame is THE model

DONE 2026-09-10. The owner's ruling: remove the non-typed path
entirely — the offset/inttoptr stack model was bad always, not an
alternative.

## Changes

- **The `--hike-stack-model` parameter is GONE** (it existed for one
  session). The offset access path is deleted; there is no selection.
- `create_addr_ptr` (renamed from `create_inttoptr` — the honest name):
  materializes the pointer for an address integer. A frame-relative
  integer is an offset from the anchor and becomes a **GEP into the
  frame**; a real (non-frame) address — section/global constants,
  foreign pointers — becomes inttoptr. That exception lane is correct
  semantics, not a model choice.
- The VSA's residency tags license the conversion (every stack access is
  tagged — the 100% Tagging Invariant); untagged addresses are foreign
  pointers and take the exception.

## Battery (the final tree)

- -O0: emission 32/32 rc=0; semantics **32 PASS / 0 FAIL**; allocas
  **160/0**; referee **2,861,148 / 0**; suite failure set == the
  pre-existing baseline (8, not this lane's).
- -O2: emission 32/32 rc=0; **pinned green 26/6** (failing set == the
  golden list); allocas 159/1 (the recorded out_struct shape-d).
- **Re-baseline: 20/32 binaries changed** vs the L1 reference — the
  deliberate, itemized re-baseline. **THE NEW -O0 REFERENCE EMISSION IS
  `/tmp/emit_typed_o0`** (byte-identity checks compare against it).
- Corpus-wide inttoptr/ptrtoint: 447 → 259 (the remainder is the
  exception lane plus the regions path's own conversions — the next
  simplification target).

## What remains open

- The 6 pinned -O2 knowns: L2 (rebase in the choke's mixed-sign spans —
  now a GEP-select in create_addr_ptr), L3 (SSE lane def-use:
  byte_copy, union_overlap, fizzbuzz_safe's residual), L4 (data-section
  relocation rendering: fptr_table).
- The 8 pre-existing unit-suite failures (owner triage).
- The remaining 259 address-int conversions (regions path + call/ret
  plumbing).
