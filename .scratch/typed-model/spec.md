# The typed-model program — convergence, soundness, simplicity

Label: ready-for-agent
Settled: 2026-09-10 (grilling sessions; decisions are the owner's);
UPDATED 2026-09-10 late: T1/T2/T6/T3/T3c landed, the -O2 corpus
incident corrected, T4's design grilled and settled, the doctrine in
its final form.
Supersedes: the open items of `.scratch/o2-attribution/`.

## Binding constraints (every ticket, no exceptions)

- **NO GATES.** No conditional refusal mechanisms, no provenance flags,
  no "if proven then … else degrade" branches. The producer's tags are
  complete; the emitter dispatches on them with complete rules.
- **NO FALLBACKS.** Every form has a complete emission rule. The only
  sound fallback is the identity (TOP / the plain access) — never
  BOTTOM, never a stop, never a silent trap.
- **THE ONE MECHANISM (owner doctrine, final form).** The symbolic
  stack base finds stack accesses (`is_stack_access` over the
  denotation), resolves call targets, and answers every producer
  question. No `is_seed` flags, no SP-derived closures, no escape
  fact, no second channel — removed, not reformed. Consumers read the
  denotations directly.
- **CONVERSION FIRST (owner directive).** Removals land as removals.
  Failures caused by a removal are INVENTORIED (gate, binary,
  reproduction command), never patched, compensated, rolled back, or
  ticketed for fixing. The model changes significantly in T4; only
  failures SURVIVING the new model get ticketed afterward. Hard bars
  that survive this doctrine: both profiles build, the instrumentation
  blocker clean, the differential referee at 0 mismatches (a soundness
  red is flagged loudly, never landed silently).
- **Soundness over precision, always.** The semantic harness is the
  oracle; the pin (`o2_known_failures.txt`) moves only in the commit
  that deliberately changes it.
- **FIX THE ARCHITECTURE, NOT THE IMPLEMENTATION (owner doctrine,
  2026-09-10 — very important).** Every failure's fix lands on the
  architecture side: construct the general rule that makes the failure
  class impossible, so the code becomes robust, general, and reachable.
  NEVER respond to a failure by adding gates, checks, or per-case
  branches at the failure site — a fix with many cases is the failure
  moving into the code. The measure of a fix: the diff deletes cases,
  it does not add them.

## Problem Statement

The typed frame is the only stack model, and the symbolic stack base
is its provenance (T3 landed; the -O2 pin moved 6→4 when the escape
died — the owner's "more precise and correct" prediction held). What
remains: stack-passed values still flow through memory and hide from
the consumer's interprocedural optimizer (the convergence class); the
SP is still threaded as a function argument instead of living in an
entry-block alloca; indirect calls still funnel through one synthetic
signature; the va_list still walks caller-window memory. The program
converts the model to its endgame form: values in registers, SP in a
slot, targets resolved by denotation — correctly first, fixes only for
what survives the conversion.

## Solution

One ordered program: T4 converts the emission convention (promotion +
the SP Slot + VSA-resolved indirect calls + internal thunks + the
renamed caller-window residual); T5 fixes the SSE lane def-use; T9
re-models va_list and retires even the window bridge; surviving
failures become tickets after T4's battery re-measures them.

## User Stories

1. As a binary-analysis consumer, I want the -O0 lift and the -O2 lift
   of the same source to optimize to equivalent results, so that my
   analysis pipeline does not depend on how the binary was built.
2. As a binary-analysis consumer, I want the optimized lift to keep
   every observable behavior of the input binary, so that lifted tools
   are trustworthy under aggressive optimization.
3. As a binary-analysis consumer, I want stack-passed values to reach
   the optimizer as call arguments, so that interprocedural constant
   propagation folds across calls (the convergence class collapses).
4. As a binary-analysis consumer, I want each sub's stack to be its
   own frame, so that recursion is reentrancy-safe and LLVM's SROA
   sees private, scalarizable storage.
5. As a binary-analysis consumer, I want indirect calls resolved by
   the VSA's denotation of the target, so that table dispatch lifts to
   direct, optimizable calls.
6. As a binary-analysis consumer, I want unresolvable indirect sites
   to stay sound through internal thunks, so that resolution failure
   costs convergence, never correctness.
7. As a binary-analysis consumer, I want SSE-vectorized code to lift
   to correct, folded results, so that optimized inputs are
   first-class.
8. As a binary-analysis consumer, I want variadic code to lift
   correctly without a stack parameter, so that the no-SP-parameter
   convention is total (the va_list re-model).
9. As the pipeline maintainer, I want the denotation to be the only
   provenance mechanism, so that there is no second channel to keep
   consistent.
10. As the pipeline maintainer, I want every emission rule complete
    per tag kind, so that no arm depends on "this cannot happen".
11. As the pipeline maintainer, I want removals to land as removals,
    so that the tree honestly reflects the model and conversion
    failures are never papered over with machinery.
12. As the pipeline maintainer, I want the convergence report to stay
    the single instrument, so that each lane's verdict states its
    movement in one place.
13. As a corpus consumer, I want the pin to fail on any unexplained
    -O2 red-list change, so that regressions and improvements are
    equally deliberate.
14. As a corpus consumer, I want indirect-call behavior covered by
    dedicated corpus sources and unit pins, so that the resolution
    classes are tested, not assumed.
15. As the pipeline maintainer, I want the surviving-failure tickets
    created only after the new model's battery, so that no lane chases
    breaks the conversion dissolves.

## Tickets

### LANDED (2026-09-10) — T1, T2, T6, T3, T3c

- **T1**: the frame-wrap license (the typed GEP requires the
  producer's frame-residency license); opt-safety 31/2 → 33/33.
- **T2**: the simplification pass (−41 LOC, structural identity).
- **T6**: section initializers render after `emit_program` through the
  code-reference map.
- **T3**: the symbolic stack base — the segment universe, the one
  denotation predicate, relativized tags, `value_env` and the frame
  relation deleted, the uniform materialization rule.
- **T3c**: the escape deleted ENTIRELY; the partition reads the
  solution's denotations; every second mechanism removed; the -O2 pin
  moved 6→4 (fizzbuzz_safe, fptr_table flip green). Inventory: the
  seed-flag denotational replacement measured red and was reverted
  (reproduction in the verdict); 21 subs honestly returned to the
  Frame model pending T4's anchor; the entry sub's SP binds via
  `llvm.stacksave` as the bridge.
- **The -O2 corpus incident**: `/tmp/corpus_o2` was a mislabeled -O0
  copy (the sp_reload-era rebuild missed the `-o2` suffix rule);
  repaired from `/tmp/corpus-o2`; `scripts/battery.sh` canary-guards
  the lanes (byte_copy/fizzbuzz_safe must differ from -O0).

### T4 (P1, NEXT) — stack-arg promotion + the SP convention

The authority is the ticket:
`.scratch/typed-model/tickets/T4-stack-arg-promotion.md` (the grilled
design, commit 5bcb538). In brief:

1. **Promotion** — per-slot, total over resolved sites: proven
   incoming slots become parameters; callers' outgoing stores become
   call arguments. Widths: promote at the stored width, narrower reads
   truncate, a wider read demotes the slot. Unprovable slots stay on
   the window (mixed per-slot).
2. **The SP Slot** — every memory-touching sub gets an entry-block
   alloca holding its per-invocation anchor (ptrtoint of its own
   frame / region base). NO sub takes an SP parameter; `hike_stack`
   and both T3 binding arms retire (plus the `llvm.stacksave` bridge
   and the `sp_restores` mechanism per the T3c handoff).
3. **Indirect calls resolve through the VSA** — the target's
   denotation classifies the site: singleton lifted sub → direct call
   through its promoted signature (a Resolved Call Site);
   multi-target/foreign/unresolvable → the pointer call through the
   Thunk. Target-authoritative signatures; sites storing fewer slots
   pass undef (reading an unpassed arg is UB in the binary too).
4. **Thunks** — internal-linkage memory-convention twins of
   address-taken promoted subs; fn-pointer data renders to the twin;
   no target ever demotes.
5. **Caller-Window Parameter** — the residual (variadic bridge +
   mixed unproven remainder), RENAMED from `hike_stack`;
   `check_allocas`' sp-roots modernize in the same commit.
6. **Tests** — four new corpus sources (`fn_table_disp`,
   `jump_table_sw`, `fn_single`, `fn_escape`; corpus 33 → 37,
   deliberate) + unit pins for the four resolution classes and the
   thunk shape (the existing Test_seam/corpus seams, no new seams).
7. **Retirement inventory** — everything in T3c's verdict BLOCKED-BY-T4
   section lands here, each item's disposition (died/bridged/
   re-attributed) in T4's verdict.

Convergence prize (measure vs the pre-T4 reference): deep_chain,
spill_many, many_args, alloca_vla, nested_calls, mixed_fp_int,
union_overlap collapse toward their o2+opt counts.

### T5 (P2) — L3: the SSE lane def-use fidelity

Re-scoped to the 4-knowns world: byte_copy and union_overlap (the L3
class), array_local's convergence gap, and whatever -O2 shapes the
four new indirect-call sources add. Lane-consuming ops must meet the
lane defs written earlier in the same iteration (the
producer-subtraction discipline); vector store loops must advance.
Blocked-by: T4 (its promotions change the measured class; the
accounting order holds).

### T9 (P2, NEW) — the va_list re-model

Retire the caller-window parameter for variadic subs: the va_list
overflow becomes model-local storage (an alloca'd overflow array the
va_list walks, populated from the promoted parameters), or the
LLVM-variadic tail — the implementer measures both against the
no-second-mechanism doctrine and lands one. va_arg_mixed and
va_arg_vacopy (the va_list state round-trip) are the measured class.
Blocked-by: T4. After T9, NO sub takes a window parameter unless a
mixed unproven remainder demonstrably survives.

### T7 — DISSOLVED (re-attributed)

The L2 mechanism is structurally deleted (T3) and the failure
persisted → the va_arg_vacopy residual is the va_list state
round-trip; T9 owns it. va_arg_mixed stays L1 (the ud2 poison arm) —
re-attributed in T4/T9's verdicts if the class moves.

### T8 — the 8 pre-existing unit failures (ROOT-CAUSED, ready to fix)

Full triage: `.scratch/typed-model/t8-triage.md`. Both groups broke at
ONE commit (`5218757`, the no-gates conversions lane — its
"runtest ALL PASSED" record was a stale run). E2eD-7/8: the pins froze
the OLD unsound dropped-store behavior; the sound conversion is
correct — RE-DERIVE the pins. LM F1 (6): the `complement_guard_op` fix
killed the landmark ACQUISITION probe's polarity (it must probe the
jump's `NOT`-aware excluded-boundary row, not the complemented flag
row) — REPAIR the probe; it is the landmark feature's only end-to-end
acceptance test. Both groups survive the T4 model unchanged (no
segment-universe involvement). The F1 repair is small and
T4-independent — sequencing is the owner's call (conversion-first says
after T4; the diagnosis is ready whenever).

## Testing Decisions

- The seams are the existing ones — no new seams: the corpus battery
  (`battery.sh`: provenance canaries → runtest+referee → emission →
  check_allocas → strict semantics → strict opt-safety → the pinned
  gate → the convergence report), the unit suite via the
  `Cbat_vsa.Test_seam` quarantine, and the probes.
- T4's indirect-call tests ride the corpus seam (new synth sources,
  both -O0 and -O2 lanes) and the Test_seam (the resolution-class
  pins) — the highest existing seams.
- A good test asserts external behavior (stdout/rc vs native) or a
  recorded metric movement — never internal representation details.
- Conversion-first accounting: a removal lane's verdict carries the
  FAILURES INVENTORY; fix tickets exist only for failures that survive
  the next model change's battery.

## Out of Scope

- Fold-recovery — the owner chose the quality-envelope bar.
- Struct-typed frames (field-GEP per cell) — LLVM SROA's job.
- Fixing inventoried failures before T4 lands — conversion first.
- Foreign-signature modeling (PLT stubs as lifted-shaped subs) — the
  pointer call with the memory convention covers them.
- Calendar scheduling — per-lane accounting only.

## Further Notes

- **S10 — the post-T4 simplification wave** is drafted:
  `tickets/S10-post-t4-simplification.md` (dead weight, the convutils
  split, the guard-decoder store-chain deletion measured post-T5, the
  post-T9 residue sweep — with the lane order and conflict classes).
  It gates at T4's merge.
- The -O0/-O2 reference emissions are `/home/tovpr/tm-battery/
  merge-t3c/emit-o0` and `.../emit-o2` (the T3c-merged tree;
  provenance bundle `54e284d5d3441228`).
- The pin is at 4 (byte_copy, union_overlap, va_arg_mixed,
  va_arg_vacopy); the incident and its guard are recorded in the
  golden file's header.
- The 8 pre-existing unit failures and their triage are recorded in
  AGENTS.md's validation blocks.
