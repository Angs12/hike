# Articles 6 + 7 exploration (2026-09-06, f67census probe)

Measured on the cleanup-8 tip with `zz_scratch_probe/f67census.exe`
(untracked scaffolding; stanza in `zz_scratch_probe/dune`, also
untracked). All numbers are wall time on this machine, `sp_escaped` +
`frame_addr_alias` per sub via the exported `Hike.Stack_model` seam, no
`src/` edits.

## Article 7 — copy-reloc scan: DEAD BY MEASUREMENT

The `copy_reloc_addrs_val` block (`hike.ml:445-495`) walks every def 3×
(`loads_and_stores` = stores+loads per sub, `stores_only` = once more)
whenever `.bss` exists — even when `copy_relocs = []`, in which case the
result is provably `[]`.

| fact | measured |
|---|---|
| binaries with 0 copy relocs (block provably returns `[]`) | **32/35** (all fixtures) |
| binaries with relocs | gcc-12: 4, grep: 6, sort: 8 |
| 3× full-program def-walk cost, worst binary (gcc-12, 1494 subs) | **0.0071s** |
| same, ls / du / sort / grep | 0.0017 / 0.0027 / 0.0011 / 0.0017s |
| same, every fixture | 0.0000–0.0001s |

The walk replicates the block's traversal exactly; the real block adds a
`Word.to_int64_exn` + short `List.mem` per Load/Store-Int — generously
10× the walk and it is still ≤0.07s worst case (0.2% of gcc-12's 33s
wall, 0.01–0.04% everywhere else). The guard
`if copy_relocs = [] then []` is 3 obviously-correct lines that save
0–7ms/binary. Per the ADR-0006 doctrine (a change that cannot measure
its own win is complexity for nothing): **do not land alone**; it rides
free the next time `convert_binary` is touched.

## Article 6 — escape analysis: REAL BUT SMALL

`frame_escapes` per sub (`sp_escaped` + short-circuit `frame_addr_alias`),
35-binary census:

| binary | subs | sp_escaped | frame_addr_alias | total | wall share |
|---|---|---|---|---|---|
| gcc-12 | 1494 | 0.385s | 0.126s | **0.511s** | ~1.5% |
| du | 761 | 0.156s | 0.026s | 0.182s | 0.6% |
| ls | 707 | 0.097s | 0.019s | 0.116s | 0.6% |
| grep | 475 | 0.111s | 0.024s | 0.135s | ~1% |
| sort | 452 | 0.063s | 0.017s | 0.080s | ~1% |
| 32 fixtures | 15–31 ea | ~0.001s ea | ~0.000s | ~0.05s | ~0% |

Corpus-35 total ≈ **1.1s** (extrapolates to ~3–5s of the 803s
coreutils wall, ~0.5%). Worst subs scale ~linearly with defs
(`__strftime_internal`: 11–13ms at 7–8k defs — consistent with
2–4 `grow()` rounds × per-def visitor allocs, though rounds were not
directly instrumented).

**The quadratic is real but bounded**: `frame_addr_alias` nests a full
def scan with a recursive exp walk per `frame_value_def` match —
O(matches × mem-defs). Worst observed: `sub_426090` (gcc-12, 132 blk /
2114 defs / 301 tags) at **34ms alone** (38% of that sub's whole 89ms
producer cost); second-worst anywhere is 4ms (`spill_many`).
Total alias ≤126ms/binary.

(Note: the probe times both halves separately and sums; the pipeline
short-circuits (`sp_escaped || frame_addr_alias`), so these totals are
slight overestimates — which only strengthens the "small" verdict.)

## Recommended shape (LANDED 2026-09-06 as `39ffcb6`: alias inverted
index only; the A7 guard was approved separately and is still pending)

One small ticket, two items, neither touching `grow()`:

1. **Alias inverted index** (`frame_addr_alias`, `hike_stack_model.ml:550`):
   collect `frame_vars` in one pass, then one pass over mem-address defs
   testing membership — O(defs + mem-defs) instead of O(matches ×
   mem-defs). LANDED as `39ffcb6` with a correction to the first draft:
   the naive free-vars sketch was WRONG (`var_maybe_addr` carries a
   here-dead sp/fp cross-match arm and deliberately no `BinOp` descent,
   so plain membership would over-taint and change IR). The landed
   version lifts the predicate itself to a target SET
   (`addr_mentions_any`); equivalence rests on (a) targets never being
   sp/fp (via `frame_value_def`), and (b) `Var.same x y =
   equal (base x) (base y)` making base-var set membership exact.
   `var_maybe_addr` deleted (private, single call site).
   Measured: alias 126ms → 47ms on gcc-12 (−63%), 34ms outlier gone
   (max 1ms anywhere); ls 19→14ms, du 26→25ms.
2. **A7 guard rides free** (3 lines, `hike.ml:445`).

Expected ticket prize: ~0.15s over the 35-gate set (~0.4s extrapolated
to coreutils-103). Explicitly NOT included: a `grow()` worklist
(moderate change + subtle fixpoint for ~0.2s — does not clear the bar)
and the `value_free_vars` visitor-alloc micro-fix (lost in the noise).
