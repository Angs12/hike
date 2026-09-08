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

## Gates

Docs-only: full battery is already green at 07's tip; this ticket must change no
code (any code smell found during the doc sweep becomes its own ticket, not a
rider). The AGENTS.md timestamp-honesty directive is the gate: an agent reading
only this section must be able to distinguish its own regressions from inherited
ones.
