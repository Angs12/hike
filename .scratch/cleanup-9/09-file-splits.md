# Ticket 09 — file splits (LAST: contents stabilize before files move)

Deps: tickets 01-08 landed (the splits reorganize what they left). One
battery-verified commit per split, smallest first — each is a pure move,
mli-frozen, behavior-inert.

Order and legality notes:
1. **hike.ml** (post-seam ~470 lines) → filter / sections / registration.
   The emitter seam already moved the sig machinery out; what remains is
   three stages + registration. Also fixes the filter-list/function name
   collision (rename the list). Pure move.
2. **test_common** (the 1876-line fixture-lib result) → harness vs
   fixtures. Two cohesive modules: the checker/aliases and the fixture
   vocabulary. The theme files' opens unchanged (re-export via include).
3. **The domain-property move** out of the regression file (rides ticket
   08 if already done — skip here if so).
4. **The memmap Key module** (~215 lines of self-contained interval
   algebra, zero deps on the memory domain) → its own domain-library file;
   the memory module re-exports so the mli is stable.
5. **The CLP engine** (~1565) → types+creation+order+lattice vs arithmetic.
   Legal: the domain library is unwrapped, siblings reference siblings.
   Cut AFTER the honest-gate's step-1/fixed_bits lane settles; the .mli
   surface does not move.
6. **The emitter** (~2375) → env / section / exp / FP / core via an
   include-chain. The 12-val seam froze the public surface — internal
   siblings cannot leak; the 73-check emission wing pins behavior at the
   new granularity (the FP-table checks live next to the FP module). Zero
   dune changes (auto-discovery; the preprocessor is library-level).
7. **The VSA engine** (~3100) → forward-transfer / backward-walk / driver.
   The legality pattern is proven: the engine's main module is the WRAPPED
   library's — siblings cannot reference it — so internals move OUT to the
   unwrapped domain library first (the run-context module set the
   pattern), then the main module re-exports the seam, mli unchanged, all
   fixtures/probes keep compiling. The walk module must not import the
   main module (a cycle by construction — ADR-0005's recorded gotcha).
   This is the big one: land it as its own lane if review prefers, with
   the two-run determinism harness as the extra gate (the exposed
   renumbering wobble is upstream — verify zero NEW residue class).
8. **Splits recorded as NOT doing**: the contextual-fixpoint Dep wrapper
   (its ADR: the backward transfer is genuinely target-dependent);
   convutils (small gain, rides the emitter split if ever); the probe
   dune stanzas (dune has no stanza templating — regenerate-on-add note
   only); the nested probe dir (owner decision, ticket 08).

Every split's acceptance: build both profiles; full battery; corpus IR
byte-identity 32/32 (a move that changes bytes is a bug); suite output
byte-identical; the frozen mlis (the library seam, the emitter seam, the
VSA engine's mli) compile UNCHANGED — that compilation is the split's
proof that no public surface moved.

Post-lane bookkeeping: AGENTS.md validation-state refresh; the architecture
appendix HTML re-anchored to the new files; CONTEXT.md gains no new terms
(the splits reuse existing vocabulary: the walk IS the deep walk, the
transfer IS the trace-partitioning transfer).
