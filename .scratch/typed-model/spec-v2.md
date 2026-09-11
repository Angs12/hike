# The typed-model program v2 — the comprehensive spec

Label: ready-for-agent
Written: 2026-09-11 (the comprehensive consolidation; supersedes
`.scratch/typed-model/spec.md`, which remains as the v1 record).
Every decision below is the owner's, settled across the program's
grilling sessions and lanes. The doctrine is the spec's binding core;
the landed record and the designed queue follow it.

## Binding constraints (every ticket, no exceptions)

- **NO GATES.** No conditional refusal mechanisms, no provenance
  flags, no "if proven then … else degrade" branches. The producer's
  facts are structured and complete; every consumer dispatches on
  them with complete rules. A boolean summary of a structured fact is
  a flag, and a flag is a seed by another name (the `site_provable`
  lesson).
- **NO FALLBACKS.** Every form has a complete rule. The only sound
  fallback is the identity (TOP / the plain access / the pointer
  call) — never BOTTOM, never a stop, never a silent trap.
- **ONE MECHANISM.** The symbolic stack base finds stack accesses
  (`is_stack_access` over the denotation), resolves call targets,
  sizes frames (only a `StackOff` proof), and answers every producer
  question. No translation layers between representations, no side
  tables, no smears — every kind, table, bridge, and side-channel
  that exists for any other reason is measured, and the denotation
  absorbs it or the evidence keeps it.
- **FIX THE ARCHITECTURE, NOT THE IMPLEMENTATION.** Every failure's
  fix constructs the general rule that makes the failure class
  impossible. The measure of a fix: the diff DELETES cases, it does
  not add them. A fix with many cases is the failure moving into the
  code.
- **CONVERSION FIRST.** Removals land as removals. Failures caused by
  a conversion are INVENTORIED (gate, binary, reproduction), never
  patched, compensated, rolled back, or pre-emptively ticketed. Only
  what SURVIVES the next model change gets fixed. Hard bars that
  survive this doctrine: both profiles build, the instrumentation
  blocker clean, the differential referee at 0 mismatches.
- **SOUNDNESS OVER PRECISION, ALWAYS.** The semantic harness is the
  oracle; the -O2 golden list moves only in the commit that
  deliberately changes it (a proven flip, labeled; any unexplained
  movement is a REGRESSION and blocks).

## Problem Statement

The pipeline lifts x86-64 PIE binaries to LLVM IR, and every analysis
fact it computed carried a fiction from the offset-model era: a fake
RSP-value universe, a syntactic escape closure, a KB side table, two
address classifications, a bridge between representations, a
flag-idiom decoder run per query forever. The lift was correct but the
*code told stories about machines that no longer exist*, and each
story was a future bug (the corpus incident, the 4-exabyte frame, the
opt-safety regression — all failures of redundant mechanisms
disagreeing). The owner's program: convert the pipeline to its
endgame form where the denotation is the only mechanism, the emitter
reads structure instead of records, and every deletion is measured.

## Solution

A single ordered program on one branch (`typed-model-program`),
driven by per-ticket verdicts on a fixed battery. The landed waves
(T1–T4b, T8, S10, the typed-flag removal, T10, T14) converted the
model; the designed queue (T13, T15, T12, T5, T9, S10c/d) finishes
the purge and the semantic frontiers. Each ticket: one mechanism
change, one verdict, the case-count delta, the pin moved only
deliberately.

## The landed record (with evidence)

| wave | what moved | evidence |
|---|---|---|
| T1 | the frame-wrap license: the typed GEP requires the producer's frame-residency proof | opt-safety 31/2 → 33/33 |
| T2 | the post-removal sweep | −41 LOC, structural identity |
| T3 | the symbolic stack base: the segment universe `[2^62, 2^62+8MiB]`, one `is_stack_access` predicate, `value_env` + the frame relation deleted, the uniform materialization rule | 7 pins re-derived; the L1 class structurally impossible |
| T6 | section initializers render after `emit_program`, through the code-reference map | the L4 mechanism |
| T3c | the escape deleted ENTIRELY; the partition reads the denotations | the -O2 pin 6 → 4 (fizzbuzz_safe, fptr_table) |
| T4 | the grilled conversion: stack args promoted per-slot (widest+trunc, written slots demote), the SP Slot (entry-block alloca, per-invocation anchor), VSA-resolved indirect calls (singleton → direct; the rest → the pointer call), internal thunks (fn-pointer data renders to twins), `hike_window` (the variadic/mixed residual), retaddr reads bind undef | all 21 re-framed subs recovered; the convergence prize (many_args 121→58/4, mixed_fp_int 136→68/4, variadic 185/27) |
| T4b | conversion correctness: Unknown seeding (TOP-addressed defs tag Unbounded), the Caller lane serves the node by value substitution, slot args consume the STORED value, written slots demote | strict -O0 32/5 → **37/37**; two unsound case-fusions deleted; +176/−94 |
| T8 | the unit suite repaired: the F1 acquisition-probe polarity fix (the fallthrough edge's own excluded-boundary row) + the E2eD pins re-derived (the sound invalidated-memory contract) | **ALL CBAT TESTS PASSED** — first time since 5218757 |
| S10a | the dead-weight wave + the region-GEP measurement (the hole exists in the dispatch, fires zero times, safe by construction) | byte-identical 37/37 both lanes |
| S10b | `convutils` deleted: the record in `Hike_stack_model`, the emitter state in `Bil2llvm_env` | byte-identical 37/37 both lanes |
| typed-flag | `typed_frame`'s option died — ONE `stack_anchor` fact (frame → `%frame`; precise → region-0), two consumers | byte-identical 37/37 both lanes |
| T10 | the intrinsic-callers filter dead (a structurally empty predicate); the promotion a BIR rewrite (`promote_sub`): real sub parameters, stored-value call args, direct resolved targets; **the emitter consumes NO record** (grep-proven; `Hike_kb` pipeline-only; geometry as a layout tag; per-def facts on the def's value) | census delta ZERO; convergence line-identical |
| T14 | the escape-extent rule: only a `StackOff` proof sizes the frame (`stack_offsets` accessor); no silent array-type truncation; absurd spans degrade | **spill_many flips; the pin 7 → 6**; the frame back to the merge-t1 shape; the band census: live by design (`_start`'s aligned-SP lane), kept with evidence |

## The designed queue (each ticketed with its evidence)

- **T13 — the jump-compiler pass.** A BIR→BIR pass compiles every
  dominating-single-def jcc idiom into the SIMPLEST equivalent value
  comparison — redesign, not relocation: reuse the def's value var,
  fold degenerate forms, width-minimal, canonical (constant-right),
  drop the consumed defs; the complexity delta is per-family census
  data. The residual (non-dominating/multi-def) stays the identity.
  The VSA's decoder rows, the complement table's flag arms, and the
  emitter's flag translation delete. The F1 landmark pins are the
  feature's acceptance. (Construction in flight: the pass + pins are
  dune-local; registration, deletions, and the battery wait for a
  slot window.)
- **T15 — the single representation.** Tags carry the DENOTATION (the
  segment WordSet, absolute); `relativize_opt`, its Option, and its
  smear arm die; exactly one relativization remains (the emitter's
  anchor subtraction). The pins re-derive with verification (values
  become absolute).
- **T12 — the kind collapse.** `Unbounded` dies into `Infinite` (TOP
  is the fully-infinite span; directional bounds). The `VLA` kind's
  storage role moves to the partition's Dynamic class (the enum
  becomes Range / Infinite / Dead); `vla_alloc_tids` stays per-def;
  **alloca_vla's dynamic alloca is the acceptance**.
- **T5 — the SSE lane def-use.** The three-point mechanism (the
  pre-digest): sequential-state producer subtraction in the deep
  walk; the Store row in `def_constraints`; the head extrapolation
  extended to cell data. Byte_copy + union_overlap are the expected
  flips.
- **T9 — the va_list re-model.** The alloca'd overflow array (decided
  by evidence: option (b) has no rule for the inlined class); the
  window parameter dies for the whole variadic class; the
  va_list-escape class is flagged if it appears. Post-T9: the
  window/Mixed residue sweep (S10d).
- **S10c — the store-chain deletion** (measured post-T5: the
  denotational `known_nonneg` replacement is measured in T5's
  verdict; green deletes ~130 lines, red grows the inventory one
  line). **S10d — the post-T9 residue sweep.**

## User Stories

1. As a binary-analysis consumer, I want the -O0 and -O2 lifts of the
   same source to optimize to equivalent results, so that my pipeline
   does not depend on how the binary was built.
2. As a binary-analysis consumer, I want the optimized lift to keep
   every observable behavior, so that lifted tools are trustworthy
   under aggressive optimization.
3. As a binary-analysis consumer, I want stack-passed values to reach
   the optimizer as call arguments, so that interprocedural
   optimization folds across calls.
4. As a binary-analysis consumer, I want each sub's stack to be its
   own frame, so that recursion is reentrancy-safe and SROA sees
   private storage.
5. As a binary-analysis consumer, I want indirect calls resolved by
   the VSA's denotation, so that table dispatch lifts to direct,
   optimizable calls.
6. As a binary-analysis consumer, I want unresolvable indirect sites
   sound through internal thunks, so that resolution failure costs
   convergence, never correctness.
7. As a binary-analysis consumer, I want jumps compiled to value
   comparisons once, so that the consumer's optimizer sees native
   comparisons and the analysis reads one representation.
8. As a binary-analysis consumer, I want variadic code lifted without
   a stack parameter, so that the no-SP-parameter convention is total.
9. As a binary-analysis consumer, I want dynamic allocations as real
   dynamic allocas, so that VLA semantics survive the lift.
10. As a binary-analysis consumer, I want the four indirect-call
    shapes covered by dedicated corpus sources, so that resolution,
    thunks, and windows are tested, not assumed.
11. As the pipeline maintainer, I want the denotation to be the only
    provenance mechanism, so that there is no second channel to keep
    consistent.
12. As the pipeline maintainer, I want every emission rule complete
    per tag kind, so that no arm depends on "this cannot happen".
13. As the pipeline maintainer, I want the emitter to read structure,
    not records, so that the analysis and the emission evolve
    independently.
14. As the pipeline maintainer, I want one representation of stack
    facts (the denotation), so that no translation layer can misfire
    (the T14 lesson).
15. As the pipeline maintainer, I want removals to land as removals,
    so that the tree honestly reflects the model.
16. As the pipeline maintainer, I want a fix's diff to delete cases,
    so that the code becomes more reachable with every repair.
17. As the pipeline maintainer, I want the unit suite fully green, so
    that its silence means green (T8's repair is the standing proof).
18. As the pipeline maintainer, I want dead probes deleted with their
    questions, so that the debug surface stays honest.
19. As a corpus consumer, I want the pin to fail on any unexplained
    red-list change, so that regressions and improvements are equally
    deliberate.
20. As a corpus consumer, I want the battery to canary-guard the
    corpora, so that a mislabeled lane can never pass again.
21. As a corpus consumer, I want every verdict to state its pin and
    convergence movement, so that the program's progress is one
    instrument away.

## Implementation Decisions

- The stack model: the typed frame is THE model — real allocas, the
  SP Slot anchor (per-invocation), regions the VSA proves
  non-overlapping, dynamic allocas for VLAs, the inttoptr Exception
  Lane only for genuinely foreign addresses.
- The call convention: no sub takes an SP parameter; stack args are
  real parameters (per-slot, widest+trunc, written slots demote);
  indirect calls resolve through the target denotation; thunks are
  internal memory-convention twins; `hike_window` only for the
  variadic/mixed residual until T9.
- The promotion is a BIR rewrite, not emitter record-reading; per-def
  facts ride the def's value; geometry rides a layout tag.
- The classification: one predicate over the denotation; the escape
  does not exist; frame sizing requires a StackOff proof; the kind
  enum collapses to Range / Infinite / Dead (+ the storage lattice
  for Dynamic).
- The flag knowledge lives once, in the jump-compiler pass; the VSA
  consumes comparisons.
- The module shape: the record in `Hike_stack_model` (the
  producer/emitter contract point); the emitter state in
  `Bil2llvm_env`; `convutils` deleted; `Hike_kb` pipeline-only.
- The diagnostics: one sanctioned channel (`Hike_diag`), loud on the
  classes that matter (Dead, unbounded spans, absurd frames), silent
  elsewhere; debug output only under the vsa-debug profile.

## Testing Decisions

- The seams are the existing ones — the corpus battery
  (`scripts/battery.sh`: provenance + corpus canaries → runtest +
  referee → emission both lanes → check_allocas → strict semantics →
  strict opt-safety → the pinned gate → the convergence report), the
  unit suite via the Test_seam, the probes.
- A good test asserts external behavior (stdout/rc vs native) or a
  recorded metric movement — never internal representation. A pin
  that freezes unsound behavior is re-derived with verification (the
  T8/E2eD precedent), never muted.
- The corpus: 37 PIE binaries, both lanes, canary-guarded; the four
  indirect-call sources are permanent members.
- Conversion-first accounting: a removal lane's verdict carries the
  FAILURES INVENTORY; fix tickets exist only for what survives.

## Out of Scope

- Fold-recovery (the owner chose the quality-envelope bar).
- Struct-typed frames (SROA's job).
- Foreign-signature modeling (the pointer call covers them).
- TID renumbering (the `simplify_jmps` class — deliberate re-baseline
  only, never a rider).
- Fixing inventoried failures before the next model change lands.

## Further Notes

- The current oracle state: strict -O0 **37/37**, strict opt-safety
  **37/37**, the unit suite **ALL PASSED**, the referee
  **2,861,148/0**, the -O2 pin at **6** (byte_copy, union_overlap,
  va_arg_mixed, fizzbuzz_safe, va_arg_vacopy, jump_table_sw — each
  owned by T5/T9/T13's lanes), convergence: the memory-passed class
  collapsed, six more sources SAME/SAME.
- The incident record: the mislabeled -O2 corpus (repaired; canary
  guard); the T4 agent's in-place corpus rebuild (recorded deviation).
- Prior art (the research note): hike's design is ahead of mctoll,
  remill/McSema, retdec, and anvill — none promotes stack args; the
  SP-as-argument belief is folklore. The battery is the oracle by
  necessity, and by choice.
