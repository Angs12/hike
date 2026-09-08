# Ticket 08 — Docs: AGENTS.md refresh + the lane's standing references

Blocking: 07. Blocks: none (lane exit).

## Change

CONTEXT.md and ADR 0008 already landed with the spec (2026-09-08, this session); this
ticket is the tree's standing documentation:

1. **AGENTS.md — the non-negotiable refresh** (the explicit directive): rewrite the
   CURRENT VALIDATION STATE section with the lane's fresh numbers and timestamp;
   record the lane in the design-principles vocabulary where it binds (the
   "Target-Defined Stack Pointer" bullet in principle #8 gains the SP-only-grant
   sentence and the fp-is-a-GPR consequence; the stack-model section's escape-rule
   prose switches from "sp/fp-derived" to the SP-seeded closure wording).
2. **Stale-reference sweep for the fp vocabulary**: `grep -rn "is_stack_reg\|fp_of\|
   is_sp_or_fp\|frame pointer" AGENTS.md docs/ src/` — every surviving prose mention
   updated to the new mechanism names (the code's zero-hit grep is T6's; the DOCS
   must not describe deleted machinery as if it existed — the 2026-08-31 doc-bug
   incident is the recorded failure mode).
3. **AGENTS.md Gotchas**: add the lane's own gotcha entries if any were learned
   (candidate: the `anchored_entry` RBP={0} seed's true meaning under the
   value-based tagging path — what the backward-lane fixtures actually test; the
   seed's DELETION belongs to the provenance lane, referenced from ADR 0008).
4. **The ADR cross-references**: ADR-0001's SP-only clause marked carried-forward
   (its superseded line names 0008); ADR-0003's two-channel description reads
   consistently with the sharpened Stack Access entry (sp-derived, not
   frame-derived-by-name).
5. **The provenance lane's placeholder**: `.scratch/sp-only-stack-semantics/`
   verdict.md records the lane's end state AND the deferred provenance lane's
   one-paragraph brief (the dual-lane bits, the channel-2 gate, the fixture
   prologue-earn migration) so the next session finds it without re-deriving the
   grill.

## Done (this session — f206faf + AGENTS.md refresh)

- Spec + ticket 06/07 updated to the no-gates ruling (commit f206faf); the
  AGENTS.md CURRENT VALIDATION STATE carries a dated 2026-09-09 entry with the
  fresh numbers, and principle #8's Target-Defined-SP bullet gains the SP-only
  grant. The remaining prose sweep of the HISTORICAL (bracketed) session records
  is optional — they are labeled records, not current-state — and the stack-model
  escape prose is already the SP-seeded closure wording.
- **AGENTS.md Gotchas — entries learned this session:**
  - **Constant-folded native-FP ops**: a fixture that feeds a CONSTANT operand
    temp (`intrinsic:x0 := 0x4059`) makes LLVM fold the sitofp/fmul away — the
    emission check sees no op. Feed non-constant operand temps to pin the REAL
    instruction. (Constant folding also masks the sig-table fallback: an undef/
    constant fallback operand is folded, and the native-op binop sidesteps LLVM's
    value modulus — a `831 := 832 mod 15` sits undeleted.)
  - **The mapped-intrinsic operand source is the STATIC table, not the sig**:
    `fp_op_inputs` resolves each operand from the block's `intrinsic:xN` temp.
    A signature-table fallback for a call target outside the sig map substitutes
    a calling-convention lane (RDI, ...) — register lanes are the -O2 GPR class
    the lane deletes, never the interface.
- The provenance lane's one-paragraph brief is in `verdict.md` (the dual-lane
  bits, the channel-2 gate, the fixture prologue-earn migration).
