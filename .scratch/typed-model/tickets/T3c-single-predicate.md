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
- Audit targets (verify conformance, change only if violated): the
  predicate uses `denote_imm_exp` (the owner phrased it as
  `denote_exp` — align the naming/structure to the denotation family
  without a functional change if the imm variant is the correct
  address denotation); `st_tag_of`'s tag-state (must be derived FROM
  the solution's denotations, not an independent channel); the
  `in_stack_segment` degraded arm (plain hulls in the non-canonical
  band — a denotational property of the value set, expected fine);
  any seed-flag-shaped machinery anywhere in the word domain or the
  transfer functions.

## The rule that replaces the closure

The escape question goes denotational: a call's pointer-argument
register ESCAPES iff, in the call block's abstract state, the
register's DENOTATION is a stack-symbolic set (`is_stack_access`'s
`in_stack_segment` on the denoted value — the same predicate family,
applied to values). No var-closure, no syntactic derivation, no
written-in-block heuristics where a denotation suffices. Whatever
`frame_escapes` feeds (the record's escape fact → split_plan/the
model's frame decisions) consumes the new fact with the same shape —
the model stays a consumer of producer facts.

## Cleanup (the second directive)

Everything the removals orphan, deleted in the same change:
`sp_derived_closure`/`sp_escaped` and their private helpers
(`def_facts` fields that only served the closure, `value_free_vars`,
`exp_escapes`, `call_arg_escapes`, `is_memory_shape` if it loses its
last consumer), plus the usual sweep (dead values, stale comments
naming the closure, mli over-exposures) — each deletion with a
no-caller proof.

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
