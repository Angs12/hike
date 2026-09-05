# C8 — Succ-Seeded WTO-Priority Worklist (replacing the recursive chaotic driver)

**Status:** spec (approved by grilling 2026-09-05; implementation NOT started)
**Tree:** `f1832dd` (main, post C1)
**Supersedes:** nothing. **Related:** ADR-0002 (the walk's inline placement is
UNCHANGED — only the visit scheduler moves); C1 spec `.scratch/c1-walk-budget/spec.md`
§2 (the budget's per-SCC recharge trigger dies with the recursive driver —
this spec redesigns it); ADR-0006 (dead avenues stay dead).
**The review:** `/tmp/opencode/architecture-review-20260905-0130.html` (C8 card).

---

## 1. Problem (the measured fact base)

The solver is recursive chaotic iteration (`stabilize_comps`/`stabilize_scc`):
whenever ANY inner block changes, the WHOLE inner component list is re-walked
in WTO order. Fresh vsa-debug measurement on the post-C1 tree (a temporary
`VISITS processed/changed/useless` print, since reverted — numbers recorded
here so they are not re-measured):

| sub | processed | changed | useless (share) |
|---|---|---|---|
| grep sub_e350 | 2,334 | 813 | **1,521 (65%)** |
| sort sub_9f00 | 975 | 342 | **633 (65%)** |
| sort sub_9570 | 974 | 432 | 542 (56%) |
| grep sub_8cb0 | 668 | 451 | 217 (32%) |

A useless visit runs the FULL `process_vertex` cost (all pred transfers incl.
inline deep walks, from-scratch `List.reduce` joins, structural `AI.equal`)
and changes nothing. The scheduler — not the domain, not the walk — is the
cost. (C1's budget cut walk pops −26.7%; the visits themselves are C8's.)

**Dead avenue, recorded (do not re-propose):** the "hybrid delta-guard"
(keep the recursive skeleton, skip provably-no-op re-visits inside it) was
considered in the grilling and REJECTED in favor of full replacement — the
skeleton's recharge/warmup/order couplings make the hybrid nearly as invasive
while capturing less. The memo-validity pre-check it needed (refuse the skip
when any pred's memo entry fired, to preserve the landmark replay) is
documented here so a future session understands what the hybrid would have
cost.

## 2. The design (grilling-settled, 13 questions)

**One mechanism: a succ-seeded WTO-priority worklist.**

1. **The queue:** priority = WTO position index (from the existing WTO list,
   built once per run); an ordered set with dedup. Pop lowest position.
2. **The seed:** the entry block's SUCCESSORS (not entry itself — entry keeps
   its init state, correctly, since it has no preds; pure entry-seeding
   deadlocks on visit 1 because a pred-less entry never "changes" and its
   successors would never enqueue. Back edges to entry enqueue it later
   through the normal rule).
3. **The rule:** pop block, run `process_vertex` COMPLETELY (no dequeue-side
   skip — memo, walks, widening ladder, budget cap all run whole, replay
   included); on `true` (changed), enqueue all Tid-CFG successors. Stop on
   empty queue or the UNCHANGED `total_processed > 6000` backstop.
4. **Dead blocks keep bottom.** Unreachable blocks are never visited and keep
   `init_sol`'s `AI.bottom` default — sound (dead code is unreachable; bottom
   is the precise answer, not a narrowing), and today's one-visit state for
   them is spurious transfer-from-bottom anyway. IR-visible in principle;
   the tag-stability gate decides.
5. **Widening: per-head warmup, K=10.** Each head joins (no widening) for its
   OWN first 10 visits; the landmark ladder from its 11th. The counter is a
   small head-tid→count map in the driver; the global `total_processed` keeps
   its max_steps backstop role only. Rationale (grilling Q11): 10 is the
   landmark-ACQUISITION window — the Finite arm needs two distance
   measurements, and only the Inf arm (no landmarks acquired) can jump to
   TOP; reaching the threshold never means widen-to-TOP. Per-head is
   uniformly more conservative than today's global rule (no head widens
   earlier; termination preserved — every head still widens eventually). Cost
   to watch: extra visits pre-widening and sub_4d2a's burn (the gate judges).
6. **C1 budget trigger: global per-run recharge.** The `stabilize_scc`-entry
   site dies with the recursive driver — a worklist has no "stabilization
   episode" event, so per-SCC allowances have nothing to refill on. Replaced
   by ONE recharge at fixpoint start: `budget := 1024 × (whole-sub
   out-edges)`, same shared cell, same `budget_per_edge` constant, same
   memo-first dynamic cap, same decrement, same counters. F1-B2 is amended to
   its behavioral core (both loops still refine independently — holds hugely;
   it becomes the starvation-regression pin). F1-B1/B3/B4 are untouched (none
   depended on the recharge site or the driver shape).
7. **Untouched:** everything inside `process_vertex` (memo order, seed
   derivation, the meet fold, the widening LADDER itself, the walk's inline
   placement per ADR-0002); `heads`/`need_map`/`head_to_blocks`/
   `block_to_head` construction; `init_sol`; the `Walk_memo`/`Transfer_memo`
   discipline; all Stages counters (plus C1's `bhits`/`psaved`).

## 3. The acceptance bar

The C1 precedent class, minus byte-identity (visit order changes globally —
it is structurally off the table; the tag gate is the oracle):

1. Unit suite: `dune runtest` — all existing checks (F1-NEQ/F1-FT exact-value
   pins included) PLUS the amended F1-B2 green. If the scheduler shifts the
   fixpoint on fixtures, the suite fails LOUDLY — that is the gate working.
2. Corpus 35/35 rc=0; `check_allocas` identical-failure-class to control.
3. BOTH semantic gates: same PASS/FAIL lists as control; 8/8 oracle.
4. **Tag-stability gate:** per-sub tag counts AND kinds on sort/grep/gcc-12
   IDENTICAL to control (subtimes `tags` column + dump_tags kind multisets
   on every heavy sub). Any movement → investigate before landing (the gate
   that caught nothing on C1 must catch whatever C8 moves).
5. A/B producer timing: 2+ interleaved rounds × 3 binaries (host ±15%),
   stage-counter attribution (visits DOWN at flat-or-better walk depth;
   `denote`/`join`/`equal` counts DOWN proportionally to skipped visits).

## 4. Files (re-locate by NAME — lines drift; anchors verified 2026-09-05)

- `src/cbat_vsa/cbat_vsa.ml` — `stabilize_comps`/`stabilize_scc` REPLACED by
  the worklist driver (same lexical site, after the WTO/`heads`/`need_map`/
  map construction, before `Stages.report`); `process_vertex` UNTOUCHED
  except the warmup line (`Core.Set.mem heads v && !total_processed > 10`
  becomes the per-head counter check); the C1 recharge lines inside the old
  `stabilize_scc` move to fixpoint start (global edges sum); the per-head
  visit-count map lives in the driver next to `total_processed`.
- `src/cbat_vsa/cbat_runctx.ml` — no change expected (cell, constants,
  out-edges all reused as-is).
- `test_cbat/test_properties.ml` — F1-B2's letter amended (comment +
   rationale; assertions hold hugely).
- `.scratch/c1-walk-budget/spec.md` §2 — trigger amendment (per-SCC →
   per-run, with the reason).
- `docs/adr/0002-single-pass-trace-partitioning.md` — one-line addendum
   (the driver changed; the walk's inline placement unchanged).

## 5. Deliberately NOT in this spec (recorded rejections)

- The hybrid delta-guard (§1 — full replacement chosen instead).
- FIFO queue (heads could widen before inner stabilization — breaks the
  Bourdoncle discipline byte-identity leans on).
- WTO-first-sweep start (rejected in grilling: re-adds the visits C8 exists
  to kill beyond the first wave; succ-seeding covers the reachable prefix).
- Per-head budget cells (refill-on-dequeue binds nothing — heads dequeue
  constantly; most of C1's win would evaporate).
- Removing the C1 budget (surrenders the landed −26.7% walk pops).
- Touching the warmup AND scheduler semantics beyond the per-head mirror
  (one variable at a time; K stays 10).
- The seed-skip identity (unsound — C1 spec §1, ADR-0002 addendum).
