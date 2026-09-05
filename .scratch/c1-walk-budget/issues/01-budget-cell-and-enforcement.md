# 01 — Steps-vs-pops verification + the budget cell + enforcement

**Status:** ready-for-agent
**Depends on:** (none — the frontier ticket)
**Blocks:** 02, 03

**READ FIRST:** the spec (`.scratch/c1-walk-budget/spec.md`, ALL of it — the
design is grilling-settled; do not re-decide), ADR-0002
(`docs/adr/0002-single-pass-trace-partitioning.md` — the walk's placement is
NOT this ticket's concern), the tree state (post-merge `e4b309c`: `Cbat_runctx`
exists; the memo is `Cbat_runctx.Walk_memo`; `refine_edge_inline` /
`refine_edge` live in `src/cbat_vsa/cbat_vsa.ml`).

**Tasks:**

- [x] **VERIFIED (orchestrator, pre-resolved):** one `steps` iteration ==
      one worklist pop. `graphlib_graph.ml:1402-1405`: the `loop` increments
      `iters` exactly once per `step` execution, and `step` pops
      `Set.min_elt works` and calls `f` on that node — `iters` counts node
      visits; `can_iter iters = iters < steps` gates BEFORE the pop. The
      walk's own `pops` counter (`incr pops` inside the `f` callback) fires
      on the same event. CONSEQUENCE: `~steps` IS the pop cap; decrement the
      shared cell inside the same `f` callback next to `incr pops` (one
      decrement per pop, exact lockstep).
- [ ] `Cbat_runctx.refine_ctx` gains `rc_walk_budget : int ref`; `mk_rctx`
      initializes it to a fresh `ref max_int` (unused until recharge).
- [ ] The recharge: at `stabilize_scc` entry in `static_graph_vsa`
      (`src/cbat_vsa/cbat_vsa.ml`), set
      `!(rctx.rc_walk_budget) <- 1024 * (out-edge count of the SCC's member
      blocks)`. The member blocks are `Hashtbl.find_exn head_to_blocks h`
      (already built); the out-edge count is the sum over those blocks of
      their jmp terms' direct-goto targets — computed ONCE per recharge
      (walk `Term.enum jmp_t` per block, count `Goto (Direct _)` targets;
      memoize per block tid in a Hashtbl built in `mk_rctx` — the
      position-hashing lesson from `73b4756`: build once, index by the
      block-set iteration, no per-visit hashing).
- [ ] The enforcement, memo-first (spec §2.4): in `refine_edge_inline`'s
      walk arm — `Walk_memo.find` FIRST (unchanged); on a miss, launch
      `refine_edge` with the dynamic cap `~steps:(max 1 (min 256
      (max 0 !budget)))` and decrement the shared cell per pop (the verified
      step unit); a budget-limited walk (cap < 256) does NOT
      `Walk_memo.add` its result (spec §2.4 — the empty-read-set trap);
      a naturally-terminated walk (pops < cap) memoizes as today.
- [ ] `Stages` counters: `budget_hits` (a walk launched with cap < 256) and
      `pops_saved` (sum over budget-limited walks of `256 - actual_pops`)
      — extend `cbat_vsa_stages.mli`, `_debug_src.ml` (real counting,
      printed on the STAGES line), `_prod.ml` (no-op). Reset in `reset ()`.
- [ ] `dune build` + `dune runtest` green (existing suite only — fixtures
      are ticket 02).

**Verification:** build green, suite green, and a manual vsa-debug
`stage_timer` run on grep sub_e350 showing `budget_hits > 0` and `pops_saved
> 0` with the walk lane down (the full A/B is ticket 03, but a smoke sign of
the mechanism working belongs here).
