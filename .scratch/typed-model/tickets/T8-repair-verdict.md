# T8 verdict — the 8 pre-existing unit failures repaired; the suite fully green

Lane: `tm/t12-kind-collapse` (the worktree was pre-created for the queued
T12 lane; this lane is T8 — the branch name stays, the verdict names the
lane). Base `f5edb31`, fixes at `c794d6d` (fix 1) and `65c72ac` (fix 2).
Authority: `.scratch/typed-model/t8-triage.md` — both groups root-caused
to commit `5218757` (the no-gates conversions lane), whose "runtest ALL
PASSED" record was a stale run.

## Baseline (pre-fix, forced runtest)

Exactly the recorded 8: E2eD-7, E2eD-8, LM F1-NEQ, F1-FT x2, F1-B1 x2,
F1-B3. Referee `clpequiv: checked=2861148 mismatches=0 both-raised=1300`.
Ok-set captured: 516 ok / 8 FAIL (524 check lines).

## Fix 1 — the landmark ACQUISITION probe (6 F1 failures)

`src/cbat_vsa/cbat_walk.ml` (`acquire_unsat_fallthrough`).

**Mechanism (confirmed against `git show 5218757`):** that commit fixed
`complement_guard_op`'s EQ row (`EQ -> EQ` was `EQ -> NEQ` now) for
false-edge STATE refinement — right — but `acquire_unsat_fallthrough`
reuses the complemented row as its `observe_unsat` probe while ignoring
the jump condition's `NOT`. For the jne-counter fixture
(`ZF := ((i-K) == 0)`, taken cond `NOT zf`, so the FALLTHROUGH edge is
the exit where `i = K`): pre-`5218757` the broken table made the probe
`{K}` — accidentally the true exit row, the landmark was acquired. Post-
fix the probe became the NEQ two-piece `TOP−{K}`, whose meet with the
growing counter is never empty — no landmark, `lm_calc_steps` = `Inf`,
plain widening, unbounded head. Six pins red.

**The repair (one general rule, no fixture cases):** the acquisition
probe is the FALLTHROUGH edge's OWN excluded-boundary row, polarity-aware
in the jump's `NOT`:

```ocaml
let op =
  match decoded_condition cond with
  | Some NEQ -> gop                       (* NOT-zf jcc: fallthrough SATISFIES the comparison *)
  | _ -> complement_guard_op gop          (* bare-flag jcc: fallthrough on the complement *)
```

**The polarity argument (paper semantics, Simon & King Listing 1 —
`observe_unsat` in `meet_var`):** the observation fires on the guard the
cycle keeps MISSING — for a while-shaped loop that is the exit edge,
i.e. the fallthrough of the looping jcc. The flag record
(`zf := (e bop c)`) gives the comparison in the flag-def's vocabulary
(`gop`); the jump condition decides which side the fallthrough lands on.
`decoded_condition` (this file's sanctioned cond decoder — no new AST
vocabulary) returns the TAKEN-edge op; its `NEQ` row is exactly the
`NOT zf` idiom, whose fallthrough SATISFIES the flag def's comparison
(`zf` true ⟹ `e bop c` holds), so the probe is `gop` itself. A bare-flag
jcc (`zf`, decoded EQ) falls through on the complemented comparison, so
the probe is `complement_guard_op gop`. Compound idioms (`NOT (CF|ZF)` →
UGT, the xor-core SLT/SLE rows) keep the pre-`5218757` behavior (the
`5218757` change touched only the EQ/NEQ rows, and this rule leaves
every non-`NEQ`-decoded cond on `complement_guard_op gop`).

**Soundness of the probe:** `observe_unsat_var` records a landmark only
on an EMPTY meet, and consumption (`translate_to`'s clamps) can never
hold the extrapolation below a value the join has actually observed — a
landmark only delays widening toward its boundary; once a real value
passes it, the extrapolation follows the join's own growth. So the probe
is a precision instrument (which boundary gets acquired), and the repair
restores the exact exit boundary `K` for the jne class. The corrected
complement table keeps serving false-edge STATE refinement, untouched.

No gates, no fixture-shape tests: the dispatch reads the polarity off
the jump condition and applies to every jcc/flag-def pair uniformly. For
non-`EQ` flag defs under a `NOT zf` jcc the rule even yields the exact
edge row where pre-`5218757` over-approximated (e.g. `zf := (e < c)`:
probe `ULT` = the true fallthrough row, was `UGE` — a sound no-op
there); the only behavior class that moves on the current corpus/tests
is the one the F1 pins own.

## Fix 2 — the E2eD-7/8 pins re-derived (2 failures)

`test_cbat/test_vsa.ml` (the E3 block). The old pins froze the OLD
UNSOUND dropped-store behavior (dates to the gate era, `4c84296`): after
storing 42 at `0x100` and 7 at a TOP address they pinned memory
"unchanged" and the `0x100` load reading exactly `{42}` — true only
because the top-addressed store was silently DROPPED (an unsound
narrowing: the store may hit `0x100`). The current rule
(`cbat_transfer.ml:158-160`, store through a TOP address → whole-memory
top) is sound and correct; the pins now assert the sound contract:

- **E2eD-7**: the pre-store memory is provable (not the whole-memory
  top — the invalidation is real), and after the top-addressed store the
  memory IS the whole-memory top (`Mem.equal mem2 (Mem.top …)`; the
  store may write any cell — invalidated, never preserved).
- **E2eD-8**: the load at `0x100` through the invalidated memory reads
  TOP (`Ws.is_top tv`) — the pre-store `{42}` is no longer provable.
  (`Mem.find` on the whole-memory top — the empty-tree representation —
  reads `Val.top`, so the top read is the rule's direct consequence.)

Check count unchanged (2 checks, re-derived in place; per test honesty:
the old assertions were deleted with the contract they froze, not
muted).

## Verification (all dune-local; NO `dune install`, NO `bap`)

| gate | result |
|---|---|
| `dune build` + forced `dune runtest` | **ALL CBAT TESTS PASSED** (rc=0) ✅ |
| referee (clpequiv, in runtest) | **2,861,148 / 0 mismatches** (both-raised 1300, unchanged) ✅ |
| ok-set diff vs the baseline | **exactly the 8**: 8 FAIL lines removed, 8 ok lines added — the 6 F1 flip FAIL→ok with IDENTICAL pin text (they were correct all along; the producer broke them), the 2 E2eD reappear as ok under the re-derived contract text; every other line identical (524 → 524 check lines) ✅ |

Post-fix run: `/tmp/t8_after_runtest.log` (baseline:
`/tmp/t8_baseline_runtest.log`, ok-sets `/tmp/t8_{baseline,after}_okset.txt`).

## Notes

- The 6 F1 pins' text was NEVER wrong — they are the landmark feature's
  only end-to-end acceptance test (`docs/trace-partitioning-plan.md`);
  the repair is producer-side, so the pins land green unchanged.
- No other file touched; the constraint surface was exactly
  `src/cbat_vsa/cbat_walk.ml` + its tests.
- The F1 class is now measured END-TO-END again: head max = K exactly
  (Finite extrapolation), taken body = K−1, fallthrough exit = {K} —
  the acquisition → consumption chain (Listing 1 → fig. 3) works.
