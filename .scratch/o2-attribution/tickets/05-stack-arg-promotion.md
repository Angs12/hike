# 05 — stack-arg promotion: values in registers, not through memory

Opened 2026-09-10 (the convergence program's first implementation lane).
Status: ready to implement.

## The problem (measured)

The -O0 lift passes inter-procedural values THROUGH STACK MEMORY: the
caller stores outgoing args into its frame's outgoing area, the callee
loads them from [rsp + k ≥ 0]. LLVM's interprocedural constant
propagation does not track values through memory, so every value flowing
through the outgoing area blinds the consumer's optimizer.

Convergence baseline (`convergence_report.sh`): the memory-passed sources
sit at huge -O0/-O2 post-opt ratios with the -O2 lift collapsing to a
printf of constants (the compiler moved the values into registers; our
lift moves them through memory):

| source | o0+opt | o2+opt |
|---|---|---|
| deep_chain | 323 | 4 |
| spill_many | 134 | 4 |
| many_args | 133 | 4 |
| alloca_vla | 95 | 4 |
| mixed_fp_int | 68 | 4 |
| nested_calls | 75 | 4 |
| union_overlap | 166 | 4 |

Micro-experiment proof: opt-21 folds straight through our `{i64,i64}`
aggregate-return convention (the mini-chain folds to `ret i64 <const>`),
so the convention is NOT the blocker — the memory-passing is.

## The mechanism insight

The correspondence caller-store ↔ callee-load is FIXED by the SysV
convention: the callee's incoming stack cells sit at
[entry_rsp + 8 + 8·i], and each caller stores the same slot relative to
the call's rsp. The VSA already tags both sides: the callee's
positive-offset reads (`offsets` tags, Range lo ≥ 0) and the caller's
outgoing stores (`outgoing_arg_stores`, plus the offset tags).

## The lane

Promote the proven pairs to direct LLVM call arguments:

- The CALLEE's incoming stack-cell loads (positive-offset, singleton
  ranges) become reads of new function parameters (one per distinct
  slot, i64, or per the loaded width).
- The CALLER's corresponding outgoing stores become direct call
  arguments at the call site.
- Slots that are unproven (Unbounded/dynamic) stay on the memory path —
  the complete-rule fallback, no gates.

## Design notes / risks

- Multi-call-site callees: the slot layout is the callee's own
  (entry-relative), so the signature is call-site independent; every
  caller maps its stores by the same k.
- Width matching: the caller's stored width vs the callee's loaded width
  must agree per slot; the tags carry the sizes.
- The `hike_stack`/`rebase` path is untouched for non-slot accesses.
- Risks: signature churn re-baselines the affected IR (deliberate);
  indirect calls cannot be promoted (they keep the memory path).

## Acceptance

- Semantics stays **33/33** at -O0; the pinned -O2 gate stays green
  (failing set unchanged unless the va_arg overflow reads are promoted —
  a stretch goal worth measuring).
- The convergence report moves: the seven sources above collapse toward
  their o2+opt counts. Each movement recorded in the lane verdict.
- The strict opt-safety gate stays at 31/2 (the two knowns) — no new
  opt-safety regressions.
