# ADR 0009 — the typed frame model (offset fiction → typed GEP)

Date: 2026-09-09 (prototype); 2026-09-10 (generalized — the offset
access path is deleted; the selection parameter is gone). Status:
accepted, THE model.

## Context

The emitted stack model materialized a per-sub frame alloca and an
"anchor" address (`ptrtoint (gep frame, K)`); every access computed an
address INTEGER and converted it with `inttoptr`. The fiction is
load-bearing (cell keying, k-position, cross-sub argument traffic) but
it leaks: guards consume the fake bits as values (the -O2
stack-realignment class, L1), alignment must be guarded at runtime
because the model cannot promise it (the trap/ud2 family, va_arg_mixed),
and every access is opaque to LLVM's alias analysis and SROA (447
inttoptr/ptrtoint ops corpus-wide).

## Decision

The typed form becomes the primary emitted model (behind
`--hike-stack-model=typed` during migration): address integers route
through the frame base as GEPs at the single choke point
(`create_inttoptr`); `inttoptr`/`ptrtoint` survive only as the documented
EXCEPTION LANE for addresses with no frame provenance (section/global
constants). Alignment becomes LLVM's business (align attributes on typed
accesses); the runtime alignment guards have no reason to exist.

Consequences:

- Simpler conversion: no anchor arithmetic in the access path; the
  escape/rebase machinery shrinks to pointer GEPs.
- More optimizable: LLVM sees typed memory; measured on the escape-class
  binary (byte_copy: post-opt 196→170 insns, 21→6 address conversions).
- The offset fiction remains ONLY inside the VSA's analysis state — and
  the guards' value-context fix (value_env) keeps it from leaking into
  reachability decisions.
- Generalization re-baselines the corpus IR (deliberate, never a rider).

## Alternatives considered

- Keeping the inttoptr model and widening conversion coverage — does not
  remove the fiction; the alignment-guard and rebase classes persist.
- A struct-typed frame (fields per cell) — maximum type info, but cell
  layout churns with every VSA range change; deferred.

See `.scratch/o2-attribution/tickets/03-typed-frame-prototype.md` for the
prototype's acceptance measurements.
