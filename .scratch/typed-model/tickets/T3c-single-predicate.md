# T3c — the single-predicate conformance + cleanup (owner directive, 2026-09-10)

The owner's directives, verbatim in spirit: there must be NO `is_seed`
and NO SP-derived closure — ONLY one predicate `is_stack_access` that
uses the denotation (`denote_exp`). The symbolic stack base answers
EVERYTHING. And everything the removals orphaned is cleaned NOW.

## What violates the doctrine in the landed T3 (a927c10)

- `src/hike_stack_model.ml:152` — `sp_derived_closure` + `sp_escaped`
  (inside `frame_escapes`): a SYNTACTIC {SP}-seeded closure (any
  non-memory def whose rhs mentions a derived var adds its lhs). This
  is the second channel the symbolic base was supposed to kill.
  Consumer: `hike_vsa.ml:46` (`frame_escapes sp target sub ~offsets
  ~arg_stores`) — the only one.
- STRENGTHENED DIRECTIVE (owner, same session): "We should only use
  the symbolic stack base to find stack accesses and use a predicate
  for that. Remove every other mechanisms!" — the mandate is REMOVE,
  not audit-if-violated:
  - `st_tag_of`'s tag-state survives ONLY if it is a pure derived view
    of the solution's denotations (the tag = the denotation minus the
    base); otherwise its uses read the denotation directly and the
    mechanism is deleted.
  - `outgoing_arg_stores` must be pure predicate output (verify).
  - Any written-in-block / syntactic heuristic feeding escape or
    frame-keeping (the call-abstraction lane's arg-register rule)
    yields to the denotational rule where a denotation suffices.
  - Any seed-flag-shaped machinery anywhere: deleted.
  - KEEP (not stack-access mechanisms): the VLA matcher (finds
    dynamic ALLOCATIONS, a different question), the structural
    address extraction (`stack_address_of_rhs` — a sanctioned kind
    test for WHERE the address exp lives), the predicate's own
    arithmetic (relativize, `in_stack_segment`'s degraded arm).

## The rule that replaces the closure — STRENGTHENED (owner, 2026-09-10)

The escape QUESTION dies entirely (owner: "using the stack_base means
we can move completely away from escape — the denotation transfers
everything to the actual stack accesses"). `frame_escapes`,
`frame_escaped`, and the escape FACT are deleted, not rebuilt
denotationally:
- `regions_of_sub`'s escape veto → the region partition decides from
  the tags/denotations alone (the unified segment universe makes all
  stack memory one address space — the veto approximated a question
  the address space answers exactly; the precision movement is
  measured and itemized in the verdict).
- the call-abstraction frame-keeping → consumes the address-range
  answer from the denotations at the call site.
- a consumer the denotations genuinely cannot serve = a flagged
  blocked-by item, never a rebuilt fact.

## Cleanup (the second directive)

Everything the removals orphan, deleted in the same change:
`sp_derived_closure`/`sp_escaped` and their private helpers
(`def_facts` fields that only served the closure, `value_free_vars`,
`exp_escapes`, `call_arg_escapes`, `is_memory_shape` if it loses its
last consumer), plus the usual sweep (dead values, stale comments
naming the closure, mli over-exposures) — each deletion with a
no-caller proof.

## OWNER DIRECTIVE (2026-09-10): removals land; failures become tickets

"Do the removals; any failures will be fixed in new tickets — trying
to solve them now will just make things more complicated!" If a gate
goes red BECAUSE of a removal, do NOT patch, compensate, or roll the
removal back: record the failure in the verdict's FAILURES→TICKETS
section (the gate, the binary/pin, the failing mechanism's hypothesis
if cheap, the exact reproduction command) and land. The orchestrator
tickets them; the follow-up lanes fix them against the clean tree.

## Binding constraints

Spec: `.scratch/typed-model/spec.md` (NO GATES, NO FALLBACKS,
soundness over precision). The battery is the oracle: -O0 strict
semantics 33/33, strict opt-safety 33/33, -O2 pinned 27/6 set == the
golden six (a movement is a proven flip only), `dune runtest` failure
set == the 8-failure owner baseline, referee 2,861,148/0, both
profiles build. Expect SMALL emission deltas only where the escape
fact changes a model decision; byte-identity is NOT the bar, honesty
about every delta is.

## Battery protocol (you hold the shared plugin slot)

`eval $(opam env)` first; after every install `bash
src/record_provenance.sh`; battery artifacts on home disk
(`/home/tovpr/tm-battery/t3c/`); never touch
`/home/tovpr/tm-battery/{merge-t1,merge-t3,t3}` or `/tmp/emit_*`.

## Acceptance

- No `is_seed`-shaped flag anywhere; `sp_derived_closure`/
  `sp_escaped` GONE (grep-clean); the ONLY classification/escape
  mechanism is the denotation predicate family.
- Full battery green per above; the pin holds at 27/6 set == six.
- Verdict file next to this ticket: what was deleted (with proofs),
  the new escape rule, the gate table, every emission delta itemized,
  the convergence rows before/after.

Worktree: `/home/tovpr/hike-t3c`, branch `tm/t3c-single-predicate`.
