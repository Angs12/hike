# T5 — Record the result and refresh the validation state

Blocked by: T4
Blocks: nothing

## Goal

The measurement earns its place only if it is recorded where the next
session will find it.

## Do

1. `AGENTS.md` — rewrite the **CURRENT VALIDATION STATE** section with
   fresh numbers and today's timestamp: the swap, the gate results, and
   the new corpus wall (target: < 600 s). Per the directive, a validation
   section that disagrees with the tree is a doc bug.
2. `.scratch/perf-profile/profile-2026-09-05-coreutils.md` — update the
   optimization-candidates section: B's measured delta replaces the
   estimated "−15…20%".
3. `zz_scratch_probe/census.ml` — keep it (decision: "keep and extend").
   Record the new baseline gauge in its header comment so the next
   session can re-run it.
4. If the win is large, consider an ADR recording the substrate decision
   (it changes a core representation with an upstream dependency:
   `Word.t = Z.t`). Offer it; do not write it unprompted.

## Gate

- `git diff` shows doc/probe changes only (no `src/` change beyond T2/T3).
- The numbers in `AGENTS.md` match the T4 gates exactly.
