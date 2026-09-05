# Single-pass trace-partitioning: fuse backward refinement into the forward fixpoint

## Decision

Replace the two-phase VSA — a forward Bourdoncle-WTO fixpoint **plus** a Phase B
post-pass (`edge_views_of` → `refine_edge` → `partitioned_states`) — with a
**single coupled pass**. Every out-edge of every block runs the **deep backward
walk** (`refine_edge` / `reverse_def_walk` + `constrain_cell_on_trace`) *inline in
`denote_jump`*, transferring the edge-refined environment into the destination
block's IN-state. **Phase B is deleted.**

The edge refinement input is BAP's **accumulated edge condition**
(`Graphs.Ir.Edge.cond` via `Sub.to_cfg`): in BAP the when-chain
(`when c1 goto l1; when c2 goto l2; goto l3`) is a block with multiple jmp
terms (first-true-wins), and `Edge.cond` — probe-verified 2026-08-30 — computes
each edge's path condition including every previous cond's negation
(`c2 & ~c1`; the unconditional tail carries `~c1 & ~c2`). This satisfies the
user directive ("for a cond every previous cond that was not true must refine;
when the last cond is TRUE the previous negative conds are used") natively —
one uniform rule for conditional, unconditional, and chain-tail edges, no
chain-specific machinery.

## Context

The original design (per `AGENTS.md`) computed a safe widened forward solution
and then refined it *exactly* in a separate post-pass, so the refinement was
never itself widened. The post-pass indirection (`edge_views_of` /
`partitioned_states` / `edge_view`) is complexity the user wants removed.
The deep walk (`refine_edge`) is already a **standalone** function driven today
only by `edge_views_of`; inlining it at the jump is a structural simplification,
not a precision change. Grilling session 2026-08-29 resolved all scoping and
soundness questions (see `docs/trace-partitioning-plan.md`).

## Considered Options

- **Keep the two-phase design (status quo ante)** — *rejected*: the user wants
  Phase B complexity gone.
- **Fuse with the shallow guard-meet only** (`inverse_denote_exp` / jcc-decoder
  pre-step, Q1=a) — *rejected*: this refines only the guard variable(s), losing
  the upstream **producer-subtraction** precision `partitioned_states` provided,
  which contradicts the requirement of *no precision reduction*; `inverse_denote_exp`
  is also a production no-op today (`ctx.sub = Some _`).
- **Fuse with the full deep walk + a change-driven cache** — *rejected by user*:
  "accept the complexity" — no cache.
- **Fuse with the full deep walk, no cache (CHOSEN)** — single pass; deep walk
  inline at every conditional jump.

## Consequences

- `edge_views_of`, `partitioned_states`, and the `edge_view` record are
  **deleted**; `static_graph_vsa_with_views` returns `sol` only (rename drops
  `_with_views`).
- `finish` (in `hike_vsa.ml`) reads each block's **IN-state** from the converged
  `sol`; `rewrite_addr` / `classify` are unchanged (they consume a `Mem.t`/`AI.t`
  state already).
- **Precision**: no reduction versus Phase B; possible improvement — refinements
  cascade downstream within one pass, and tighter states reach the widen so the
  fixpoint stabilizes in fewer iterations. Loop heads are unaffected (always the
  full-range join of incoming edges).
- **Cost**: the deep walk runs on every forward iteration (accepted).
- **Landmarks**: preserved by construction (the walk's meets fire
  `observe_unsat_var`; `widening_at_head` is bound around `denote_block_with_stores`).
- **NEQ / non-convex guards**: inherited `None`→identity limitation (the -O2
  `w_big` class); explicitly *not* a regression of this change.
- Code comments citing deleted Phase B `§`-numbers must be cleaned during
  implementation.

## Validation gates to re-run after implementation

- `dune runtest` (target: all pass)
- `bash scripts/run_corpus.sh /tmp/corpus /tmp/heritage_<tag>` (target: 31/31 rc=0)
- `bash scripts/check_allocas.sh <out>` (target: 124/0)
- `bash scripts/semantic/run_semantic_all.sh` (target: 31/31)
- `bash scripts/semantic/run_semantic.sh` (target: 8/8)

## Addendum (2026-09-05): the walk is now budget-bounded per SCC

The inline deep walk's cost is BOUNDED by the C1 walk-pop budget (spec:
`.scratch/c1-walk-budget/spec.md`; the placement above is UNCHANGED — the
walk still runs inline at every conditional jump). The budget does not
change this ADR's semantics: a truncated walk was ALWAYS the sound
coarsening (the `~steps:256` cap is this design's own precedent), and the
budget only chooses where the cap lands — `min(256, remaining)` of a
per-SCC allowance (`1024 × the SCC's out-edges`, recharged at every
`stabilize_scc` entry, memo-first so free precision is never refused).
Measured: grep −4.8% / gcc-12 −2.5% producer, e350's walk pops −26.7%
(467,456 → 342,548, arithmetic exact against the bhits/psaved counters),
tag counts and kinds IDENTICAL across all 2,421 real-binary subs, IR
byte-identical 35/35 — the coarsening never crossed the TAG states. The
soundness statement is one line: a shorter walk is the sound coarsening
the 256 cap always was; NO gates, NO skips (principles #2/#3). The
seed-skip alternative was proven UNSOUND during the design grilling (a
no-op Var seed can still produce new cell meets backward through a Load
def or a Load-valued phi) — recorded so it is not re-proposed.
