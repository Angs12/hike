# T8 triage — the 8 pre-existing unit failures, root-caused (2026-09-10)

Read-only diagnosis (bisect + hunk-revert, repo untouched). Both groups
broke at ONE commit: `5218757` ("vsa: the no-gates conversions land in
the vendored library", simplification-program lane 3, 09-09). Its
"runtest ALL PASSED" claim (and the follow-up record `7e7bd26`) is
factually wrong — consistent with the recorded /tmp-filled mid-lane
hazard (a stale/partial run). Not T3/T3c fallout; T3c measured the set
staying exactly 8 with `has_seed` intact, and neither group touches the
segment universe.

## E2eD-7/8 — the top-addressed-store conversion (sound fix, dead pins)

The pins (`test_cbat/test_vsa.ml:536-558`) call `Test_seam.denote_def`:
store 42 at concrete 0x100, then store 7 at a TOP address, and pin (7)
memory unchanged, (8) the 0x100 load reading exactly {42}. The breaker
hunk `cbat_transfer.ml:158-160`:

```ocaml
if WordSet.is_top addr
(* The store may write any cell: whole-memory top. *)
then return_mem @@ Mem.top (Mem.get_idx mv)
```

Before `5218757` this arm was `return_mem mv` — the store was silently
DROPPED: an unsound narrowing (a store to an unknown address may hit
0x100), which the pins froze (the pin text dates to the gate era,
`4c84296`). Post-conversion env2's memory is `Mem.top`, so (7) fails
and (8) finds no cell. **Verdict: RE-DERIVE the pins** — new contract:
after the top store, the 0x100 load reads top (or ⊇ {42,7}).
T4-independent.

## LM F1 (6 failures) — `complement_guard_op` killed landmark ACQUISITION polarity

Proven by hunk-revert: reverting only `complement_guard_op`
(`cbat_walk.ml:1124-1131`, `EQ -> NEQ | NEQ -> EQ`, was `EQ -> EQ`)
makes all 6 green; E2eD stays red. Chain: the fixture
(`test_properties.ml:357-399`) is a jne-counter loop whose upper-bound
pins (head max = K, taken body max = K-1) are delivered ONLY by
landmark consumption. `acquire_unsat_fallthrough`
(`cbat_walk.ml:1524-1552`) is the paper's `observe_unsat` probe; it
computes the probe op as `complement_guard_op(guard_op_of_binop bop)`
(1538-1539), complementing the flag def's comparison while ignoring the
jump condition's `NOT`. Pre-`5218757`, the buggy `EQ -> EQ` row made
the probe `{K}` — accidentally RIGHT for this shape, so the upper
landmark K was acquired. Post-fix the probe becomes the NEQ two-piece
`TOP−{K}`, whose meet with the growing counter is NEVER empty → no
landmark → `lm_calc_steps` = `` `Inf `` → plain widening → unbounded
head. The fix itself is correct for false-edge STATE refinement; the
regression is that `complement_guard_op` serves two roles, and
acquisition needs the excluded-boundary (comparison-TRUE) row,
polarity-aware in the jump's `NOT`.

**Verdict: REPAIR the acquisition probe** (the pin text stays correct —
it is the only end-to-end acceptance test of landmark consumption,
`docs/trace-partitioning-plan.md:105`). Suggested shape (owner's call,
not implemented): in `acquire_unsat_fallthrough`, probe the fallthrough
edge's own row — for a jump condition that negates the flag (`NOT zf`),
that is `gop` itself, not `complement_guard_op gop`; keep the corrected
complement table for state refinement.

## Per-failure verdict table

| failure | breaker | verdict |
|---|---|---|
| E2eD-7 | top-store → `Mem.top`, `cbat_transfer.ml:158-160` | re-derive the pin (it froze the unsound dropped store) |
| E2eD-8 | same hunk | re-derive (exactness through an invalidated memory is unsound) |
| F1-NEQ head max = K | `complement_guard_op` via the acquisition probe, `cbat_walk.ml:1538-1539` | repair the probe (polarity-aware row) |
| F1-FT ×2 | same | repair (shares `lm_jne_run`) |
| F1-B1 ×2 | same | repair |
| F1-B3 | same | repair |

## Reconciliation with T3c's prove_nonneg record

Complementary, independent: T3c's reverted denotational replacement of
`prove_nonneg` flipped L-D2/L-D6 (they pass today only via the
store-chain, `has_seed` at `cbat_walk.ml:268-278` — the
BLOCKED-BY-T4 item). The 8's mechanisms are independent of
`prove_nonneg` and of the cell-key universe (E2eD: plain concrete/top
addresses; F1: no memory, no stack values at all) — both survive the
SP-Slot model unchanged. F1 is a SOUND precision regression
(over-approximation; doctrine-compliant to ship red), but retiring it
would leave the landmark feature unobserved.
