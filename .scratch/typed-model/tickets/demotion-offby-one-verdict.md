# Verdict: the written-slot demotion off-by-one — FIXED (micro-fix lane)

Date: 2026-09-11. Worktree `/home/tovpr/hike-cov`, branch `tm/coverage`,
commit `d6fce42` (fix + pin), verdict at the lane tip. Fixes the
coverage lane's headline finding (`coverage-gap-verdict.md` above in
this directory — its disposition line anticipated exactly this
one-line correction). Provenance: plugin bundle `47c88fee708d0b44`,
src `15162b9f336ade5b`.

## The corrected rule

`src/hike_vsa.ml`, `callee_side`'s T4b written-slot demotion. Slot i
spans `[entry_rsp + 8 + 8i, entry_rsp + 8 + 8(i+1))`; a Caller store
at window offset `k` (bytes `[k, k+bytes)`) demotes EXACTLY the slots
its bytes intersect:

- `first = (k - 8) / 8` (unchanged — was correct)
- `last  = (k - 8 + bytes - 1) / 8` (was `(k + bytes - 1) / 8` — the
  window base `-8` had leaked out of the upper bound)

The lane now binds `rel = k - 8` once and derives both bounds from it,
so the two divisions cannot drift again. Integer-division corners:
NONE — the existing guard `k >= 8` keeps `rel >= 0` and
`rel + bytes - 1 >= 0` (bytes >= 1: BIL sizes are >= 8 bits), and
OCaml's `Int64.div` truncates toward zero, which equals floor on
non-negative words. The old code had no negative-k path either (same
guard); the bug was purely the missing base, not a rounding mode.

## The boundary-case table

Verified against ground truth (the set of cells `[8+8i, 16+8i) that
`[k, k+bytes)` actually intersects), computed independently:

| k (window off) | bytes | fixed {first..last} | buggy {first..last} | truth | buggy over-demotes |
|---:|---:|---|---|---|---|
| 8  | 8 | {0}    | {0, 1}    | {0}    | slot 1 |
| 9  | 4 | {0}    | {0, 1}    | {0}    | slot 1 |
| 15 | 8 | {0, 1} | {0, 1, 2} | {0, 1} | slot 2 |
| 16 | 8 | {1}    | {1, 2}    | {1}    | slot 2 |
| 8  | 1 | {0}    | {0, 1}    | {0}    | slot 1 |
| 9  | 8 | {0, 1} | {0, 1, 2} | {0, 1} | slot 2 |
| 23 | 8 | {1, 2} | {1, 2, 3} | {1, 2} | slot 3 |
| 24 | 8 | {2}    | {2, 3}    | {2}    | slot 3 |
| 16 | 4 | {1}    | {1, 2}    | {1}    | slot 2 |
| 31 | 1 | {2}    | {2, 3}    | {2}    | slot 3 |

The buggy formula over-demoted exactly one extra slot for EVERY
demoting write; the fixed formula is exact on every case.

## The pin (the one the coverage lane refused to write)

`test_cbat/test_model.ml`, PR-A4 extended: the fixture stores 8 bytes
at `[RSP+8]` (slot 0's cell) and loads BOTH `[RSP+8]` and `[RSP+16]`:

- `PR-A4: a window store forces the Caller-Window Parameter` (pre-existing)
- `PR-A4: the slot the store touches demotes (its read takes the window)` (pre-existing)
- **`PR-A4: the demotion is EXACT — an 8-byte store at [RSP+8] leaves slot 1 promoted`** (NEW: `prom_slots[slot-1 read] = Some 1`)

Proven RED on the buggy tree (src fix stashed, pin intact: the new
check FAILED, the two old checks stayed ok — why the coverage lane's
A4 could not see the bug) and GREEN on the fixed tree.

## Gates

| gate | result |
|---|---|
| build, default + vsa-debug profiles | rc=0 ✅ |
| `dune runtest --force` | **614 ok / 0 fail** (613 + the pin), clpequiv referee **2,861,148 / 0 mismatches** ✅ |
| instrumentation blocker | clean (run inside the battery's runtest gate) ✅ |
| -O0 emission / structural asserts | 37/37 rc=0 / **185-0** ✅ |
| **-O0 strict semantics** | **37 PASS / 0 FAIL** ✅ |
| -O0 strict opt-safety | **37 PASS / 0 FAIL** ✅ |
| -O2 emission / structural asserts | 37/37 rc=0 / **185-0** ✅ |
| -O2 pinned semantics | **31 PASS / 6 FAIL, set == the golden six** (byte_copy, fizzbuzz_safe, jump_table_sw, union_overlap, va_arg_mixed, va_arg_vacopy) — pin HELD ✅ |
| convergence vs merge-t13rev | line-for-line identical except struct_by_value (below); the other diff lines are the knowns' segfault/SIGILL PIDs ✅ |
| provenance | bundle sha16 `47c88fee708d0b44`, tree `/home/tovpr/hike-cov`, git `d6fce42` ✅ |

Battery: `bash scripts/battery.sh /home/tovpr/tm-battery/demofix demofix`
— **0 hard red(s)**, summary
`/home/tovpr/tm-battery/demofix/battery-demofix.summary`. Reference for
the delta: `/home/tovpr/tm-battery/merge-t13rev/emit-{o0,o2}` (the
latest green battery, tree `/home/tovpr/Documents/hike`). NOTE: the
battery's gate-name strings still read "33/33"; the corpus is 37 bins
and every gate ran over all 37 (the emit logs carry 37 rc=0 rows) —
stale label, not a coverage gap.

## The emission delta (attributed: this fix)

Exactly ONE binary changed, and it is the intended precision gain:

- **-O0 `struct_by_value`** (only delta; -O2 lane byte-identical 37/37):
  in the copy-out sub, the store of the SECOND stack-arg word
  (window slot 1) previously sourced a `load` through `%hike_window`
  (the over-demotion had thrown slot 1's parameter away, forcing a
  window round-trip); it now sources the promoted parameter `%1`
  directly. Downstream SSA renumbering only. Convergence quality row:
  **149/4 → 145/4** post-opt instructions (4 fewer), classification
  SAME/SAME unchanged.
- **No pin movement**: the -O2 pinned failing set is EXACTLY the golden
  six; no newly failing (no regression), no golden-listed binary
  flipped (union_overlap/va_arg_mixed/va_arg_vacopy emit IR deltas? NO —
  their -O2 emissions are byte-identical; the earlier apparent -O2
  delta was read mid-battery and does not exist).
- The other golden members' classes (L1 poison arms, L3 SSE, jump
  dispatch) are upstream of the callee-side demotion — no interaction,
  as expected.

The promoted-parameter precision the fix recovers is the
window-traffic class the program is shrinking (the many_args/
mixed_fp_int convergence levers); the corpus shows one honest,
oracle-green instance of it.
