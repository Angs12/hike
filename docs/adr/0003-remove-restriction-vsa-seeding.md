# Remove the relevance restriction — VSA-self-seeded stack accesses

## Decision

Delete the relevance pass and the `relevant`-tag restriction entirely. Every
def is denoted; the VSA seeds stack accesses itself. A Load/Store def is a
**Stack Access** iff the VSA proves its address frame-resident by either
channel: (1) **direct** — the address is affine over frame-derived registers
(`rewrite_addr` succeeds on the pre-def state's frame relation; widened
frame-affine addresses still seed — `Infinite` stays a live classification);
or (2) **reloaded** — the address's denotation is a bounded value set that is
a **SUBSET** of the frame neighborhood. Channel 2 is the saved-address class
(a stack address stored to a cell and reloaded); WYSINWYX-3's offset
representation makes the reloaded address resolve to the same abstract cell
key as a direct access. The `stack_access` and `relevant` tags are deleted;
`vsa_info` is the only carrier of stack-access-ness, making the 100% VSA
Tagging Invariant structural. VLA detection relocates into the VSA. Full
spec: `.scratch/restriction-removal/spec.md`.

## Considered Options

- **Inline relevance into the VSA (T04: `sp_derived_vars` in the AI lattice)**
  — rejected: a wide expand-contract refactor that still leaves the
  memory-carried class untracked (register-level provenance does not see a
  stored-then-reloaded address) and leaves the escape lane's L-E2 gap (the
  deleted `is_arg_setup`) unfixed.
- **Keep the restriction, extend the tagger with a memory taint** — rejected:
  a second syntactic fixpoint approximating a fact the VSA's frame relation
  already computes; the tagger's forward pass and the VSA's frame relation
  are the same fact computed twice.
- **Keep the restriction for speed** — rejected on measurement: corpus
  fixpoint time is 0.0 s per binary; the restriction's cost control is
  delegated to a measured coreutils differential with an explicit
  denotation-cheapening trigger instead (a cost bound, never a gate).
- **BAP `bap-taint` as the mechanism** — rejected: Primus-based (dynamic,
  per-path machines); its direct/indirect relation vocabulary maps cleanly
  onto the problem but its engine does not fit a static monotone fixpoint.

## Consequences

- The escape lane (call abstraction) goes live wholesale: every call block's
  arg defs are tracked, so the pointer-arg escape set reads real values; the
  caller's frame survives calls unless a pointer arg genuinely escapes. The
  whole-memory-top fallback stays for real doubt (non-singleton RSP,
  unbounded arg) — soundness unchanged.
- Channel 2 seeds on SUBSET, never INTERSECTION: a TOP/heap-valued reloaded
  address never seeds (raw-memory fallback). Non-seeding is always sound.
- The backward lane loses its refineable gates (`meet_var`, `constrain_cell`,
  the Phase B pruning): AGENTS.md principle 2 violations die with them. The
  un-gated walks restore Var-operand meets (production Phase B's were no-ops
  via `refineable = None → false`), re-arming the backward refinement fully —
  with cost held by the measured differential, not by gates.
- The emitter's `is_stack_access` becomes "carries a `vsa_info` tag"; the
  tag-vs-info divergence class disappears by construction.
- Supersedes ADR-0001's two-tag contract (the `relevant` half) and T04.
  Expected gate churn: unit fixtures drop `tag_all`; manually
  `stack_access`-tagged fixtures must be rewritten to channel-seedable
  shapes; `check_allocas` counts may rise (more tagged defs, assert is
  0-failed); the 3 known semantic failures keep T02/T03 (removal does not by
  itself close them).
