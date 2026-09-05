# The backward transfer is genuinely target-dependent — the contextual Dep wrapper stays

## Decision

The `Dep` wrapper in `Cbat_contextual_fixpoint` (`src/cbat_vsa/cbat_contextual_fixpoint.ml:17`)
will not be removed or bypassed. The backward transfer function genuinely depends on its
`~target` argument, so returning `Const` from it would be unsound. Profilers seeing
`caml_apply2` at ~10% of wall time must not treat the wrapper as dead overhead.

## Rationale

The contextual fixpoint has exactly one caller: `refine_edge`
(`src/cbat_vsa/cbat_vsa.ml:1507`), the Deep Walk. Its transfer builds, per visited block,
`fun ~target:t -> route_phi_constraints ~sol env t base b`
(`src/cbat_vsa/cbat_vsa.ml:1534-1536`). The target `t` selects which predecessor's phi
values receive the propagated constraints — different incoming edges of the same block
produce different live sets. A transfer result that ignored `~target` would conflate
per-edge refinements and lose the branch sensitivity that Trace-Partitioning exists to
provide (ADR-0002, single-pass design).

Consequences for the wrapper:

- `f` (`cbat_contextual_fixpoint.ml:61-64`) must return `Dep`; there is no static
  target-independence to exploit.
- `ctxed_equal` (`:38-43`) returning `false` for any `Dep` is conservative but sound:
  two closures cannot be compared without evaluating them at every target, which
  costs more than the iterations it would save.
- `ctxed_merge` returning `Const` for `Const`/`Const` pairs (shipped in candidate 8)
  is the only sound simplification: it fires for not-yet-visited nodes and shortens
  the fixpoint without changing its result (pinned by the F1-NEQ/F1-FT fixtures).

Measurement context (2026-09-05): `caml_apply2` was 10–11% of wall on the pre-ctxed tree
(perf `cpu_core/cycles`, `/usr/bin/{grep,ls}` worst subs). That share is diffuse — it fires
for every two-argument closure program-wide (`~f:` in all Map/List/Seq folds), not for the
contextual wrapper specifically. The wrapper's individual contribution was never isolated
(it shipped inside candidate 8's −5.16% package); a post-change profile is pending to
confirm the remainder before any further action.

## Considered options

- **Return `Const` from `f`** — rejected as unsound: discards the per-target phi routing,
  conflates edge refinements.
- **Compare `Dep` values by evaluating at the current node** — rejected as unsound:
  equality at one target does not imply equality at others; missing a change at an
  uncompared target drops a live constraint.
- **Remove the contextual layer entirely (plain Graphlib fixpoint)** — rejected: loses
  per-edge refinement, the precision the landmark-consumption fixes depend on.
- **Hand-rewrite hot `~f:` closures as manual loops** — not scoped: diffuse, marginal,
  unmeasured, and against codebase style. Revisit only if a future profile attributes
  a specific, large share to an identified closure.

## Consequences

- `Dep`, `ctxed_merge`'s fallback arm, and `ctxed_equal`'s `false`-for-`Dep` stay as-is.
- Future `caml_apply2` investigations must attribute a specific closure before proposing
  work; “remove the wrapper” is off the table and need not be re-derived.
- If the pending post-change profile shows `caml_apply2` still dominant with no single
  attributed site, candidate 7 closes as “partially done, remainder fundamental + diffuse.”
