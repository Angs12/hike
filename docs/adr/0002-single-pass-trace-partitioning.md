# Single-pass trace-partitioning: fuse backward refinement into the forward fixpoint

## Decision

Replace the two-phase VSA — a forward Bourdoncle-WTO fixpoint **plus** a Phase B
post-pass (`edge_views_of` → `refine_edge` → `partitioned_states`) — with a
**single coupled pass**. At every conditional GOTO (`Bil.If(c, t, f)`), run the
**deep backward walk** (`refine_edge` / `reverse_def_walk` + `constrain_cell_on_trace`)
*inline in `denote_jump`*, transferring the two refined environments — taken
refined by `c`, fallthrough refined by `¬c` — into the destination blocks' IN-states.
**Phase B is deleted.**

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
