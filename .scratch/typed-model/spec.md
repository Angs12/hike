# The typed-model program — convergence, soundness, simplicity

Label: ready-for-agent
Settled: 2026-09-10 (grilling sessions; decisions are the owner's)
Supersedes: the open items of `.scratch/o2-attribution/` (tickets 01–04
landed; their remaining findings are absorbed here).

## Binding constraints (every ticket, no exceptions)

- **NO GATES.** No conditional refusal mechanisms, no provenance flags,
  no "if proven then … else degrade" branches. The producer's tags are
  complete; the emitter dispatches on them with complete rules.
- **NO FALLBACKS.** Every form has a complete emission rule. The only
  sound fallback is the identity (TOP / the plain access) — never
  BOTTOM, never a stop, never a silent trap.
- **Soundness over precision, always.** The semantic harness is the
  oracle; the pin (`o2_known_failures.txt`) moves only in the commit
  that deliberately changes it.

## Problem Statement

The typed frame model is now the only stack model, and it delivered
(array_local flipped, factorial split, byte_copy's conversions halved).
But the program that makes both the -O0 and the -O2 lifts converge to
the same optimized result is unfinished: two sources miscompile after
the consumer's optimizer (a typed-model regression), six -O2 sources
still diverge (the known classes), the provenance machinery still
carries a fiction the typed model no longer needs, and the changes and
removals left cruft behind.

## Solution

One ordered program: fix the regression, simplify what the removals
orphaned, replace the provenance fiction with a symbolic stack base and
a single denotation predicate, promote stack args to registers, fix the
SSE lane def-use and the data relocations — each ticket behind the full
battery, each verdict reporting convergence movement.

## User Stories

1. As a binary-analysis consumer, I want the -O0 lift and the -O2 lift
   of the same source to optimize to equivalent results, so that my
   analysis pipeline does not depend on how the binary was built.
2. As a binary-analysis consumer, I want the optimized -O0 lift to keep
   every observable behavior of the input binary, so that lifted tools
   are trustworthy under aggressive optimization.
3. As a binary-analysis consumer, I want struct-copy-heavy programs
   (nested_struct, struct_by_value) to survive opt-21 -O2 unchanged in
   behavior, so that the typed model is safe for memory-dense code.
4. As a binary-analysis consumer, I want the SSE-vectorized -O2 code
   (lane webs) to lift to correct, folded results, so that optimized
   inputs are first-class.
5. As a binary-analysis consumer, I want data-section pointers
   (relocated constants) to resolve to real lifted addresses, so that
   indirect calls through tables work.
6. As the pipeline maintainer, I want the VSA's provenance to be one
   denotation predicate over a sound word domain, so that there is no
   second mechanism to keep consistent.
7. As the pipeline maintainer, I want the offset fiction gone from the
   word lane, so that guard expressions evaluate on sound values by
   construction and value_env stays deleted.
8. As the pipeline maintainer, I want every emission rule to be complete
   per tag kind, so that no arm depends on "this cannot happen".
9. As the pipeline maintainer, I want the Dead classification loud
   (warned) and rare, so that silent misclassifications surface.
10. As the pipeline maintainer, I want post-removal dead code deleted in
    the same program that removed the feature, so that the tree stays
    honest about what exists.
11. As the pipeline maintainer, I want stack-arg traffic promoted to
    call arguments, so that the consumer's interprocedural optimizer can
    see values that the model currently hides in memory.
12. As the pipeline maintainer, I want the convergence report to stay
    the single instrument, so that each lane's verdict states its
    movement in one place.
13. As a corpus consumer, I want the pin to fail on any unexplained
    change to the -O2 red list, so that regressions and improvements are
    equally deliberate.
14. As a corpus consumer, I want the -O0 gate to stay 33/33, so that the
    primary oracle never regresses while -O2 work proceeds.
15. As the pipeline maintainer, I want the 8 pre-existing unit failures
    triaged, so that the suite's silence means green.

## Tickets

### T1 (P0) — the typed-model opt-safety regression

nested_struct and struct_by_value: unoptimized correct, post-opt-21
DIFF (strict gate 31 PASS / 2 FAIL on `/tmp/emit_typed_o0`). Align-1
hypothesis tested and rejected; the failing set is stable; the
single-pass auto-bisect exonerates every pass → a pass-combination
interaction. The fix must be the GENERAL address-materialization rule
(the one rule every access goes through), never a per-shape patch.
Diagnose via per-pair bisection and the IR delta against the
offset-model emission (`/tmp/emit_l1_o0`, opt-green for both).
Owner: emitter/typed-model. Size M.

### T2 (P1) — the simplification pass

Sweep everything the removals orphaned: dead values (e.g.
`equal_int64_pair`), stale comments mentioning deleted machinery, mli
over-exposures, unused fixture builders. The tree carries no dangling
references after this pass. Size S.

### T3 (P1) — the symbolic stack base + single-channel tagging

Seed entry RSP's word with the bounded model stack segment
(`[2^62, 2^62 + 8MiB]`); one predicate `is_stack_access addr st` = the
denotation is a bounded set inside the segment; the tag = the denotation
minus the base. Delete the frame relation and `value_env` — the L1 class
is structurally impossible (bitwise/compares on segment words go
TOP-unknown). Includes the 7-pin modernization (the cell-key universe
shift) and the segment-word consistency of the memory lane. The failed
WIP's lesson is recorded: the seed without relativized tags broke 22/33
— the flip is one coordinated change, validated end-to-end. Size M.

**The general rule this ticket installs (and which subsumes the old
per-tag address dispatch): every address word materializes as ONE
uniform step — `ptr = frame + (word − stack_0)` — total over all words,
all signs, all widths. No positive/negative arms, no rebase selects, no
span cases. The old per-tag dispatch (singleton-positive rebase,
negative GEP, dynamic inttoptr) is deleted by this rule, and with it the
L2 mixed-span special case.
[LANDED 2026-09-10: the Mixed class (two-sided/wrapped spans — the
va_list reg-save-or-overflow pointer) materializes via the two-base
rule `select(word >= stack_0, hike_stack + (word - stack_0), raw word)`
— argued a complete rule, not a gate: the condition is exact (the sign
of the anchor-relative offset IS the boundary), both arms materialize
soundly, the rule never refuses; no single base is sound (measured).
See the T3 verdict; the "no selects" letter above is amended to "no
tag-shape dispatch arms".]

### T4 (P1) — stack-arg promotion

ALL stack args pass as call arguments — uniformly. The SysV convention
fixes the correspondence (the callee's incoming slots at
[entry_rsp + 8 + 8·i]; each caller stores the same slot relative to the
call's rsp), so the promotion is total: the callee's incoming stack
reads become parameters, the caller's outgoing stores become call
arguments — no provenness condition, no per-slot cases. Convergence
prize: the memory-passed class (deep_chain 323/4, many_args 133/4,
spill_many 134/4, nested_calls 75/4, alloca_vla 95/4, mixed_fp_int
68/4, union_overlap 166/4). Size M.

### T5 (P2) — L3: the SSE lane def-use fidelity

byte_copy, union_overlap, fizzbuzz_safe's residual, array_local's 0.18
convergence gap: lane-consuming ops must meet the lane defs written
earlier in the same iteration (the producer-subtraction discipline), and
vector store loops must advance. The biggest convergence lever after
T4.

### T6 (P3) — L4: data-section relocation rendering

fptr_table: relocated data words (`R_X86_64_RELATIVE` addends) must
render as lifted-world addresses, not raw original vaddrs. Size M.

### T7 — DISSOLVED into T3

The mixed-sign span GEP-select was a special case by construction. Under
T3's uniform materialization (`frame + (word − stack_0)`, total over all
words), there are no sign cases and no selects. Any va_arg overflow
residual is re-attributed after T3 lands.

### T8 — the 8 pre-existing unit failures (owner triage)

E2eD-7/8 and the LM F1 pins fail on the pristine tip (measured via
`git stash`); ready-for-human.

## Testing Decisions

- The seams are the existing ones — no new seams: the corpus battery
  (`run_corpus` → `run_semantic` → `check_allocas` →
  `run_semantic_opt`), the unit suite + the differential referee, the
  convergence report, the pin, and the probes (`dead_diag`,
  `width_diag`, `dump_tags`).
- A good test asserts external behavior (stdout/rc vs native) or a
  recorded metric movement — never internal representation details.
- Per-lane accounting: every ticket's verdict reports its red-list
  movement; the pin moves only deliberately.

## Out of Scope

- Fold-recovery (re-materializing computations the -O2 compiler folded
  into constants) — the owner chose the quality-envelope bar.
- Struct-typed frames (field-GEP per cell) — deferred; per-access
  splitting is LLVM SROA's job under the typed model.
- Calendar scheduling — per-lane accounting only.

## Further Notes

- The new reference emission is `/tmp/emit_typed_o0` (33/33 semantics;
  provenance src=a1253ff6826d632e bundle=96dd7386358c5dbd).
- The segment-seed WIP was reverted (broke the corpus 22/33): the seed
  without relativized tags and keys is unsound-by-incompleteness — T3 is
  the full coordinated flip, not a seed.
- The 8 pre-existing unit failures and their triage are recorded in
  AGENTS.md's validation blocks.
