# Cleanup-9: the 92-candidate readability lane — deletions, merges, hoisting, helpers, ref→fold, splits

Status: **ready-for-agent** (synthesized from the 2026-09-07 architecture
review; test seams settled with the owner: battery-only, zero new seams).
Evidence appendix: the full per-candidate, line-verified report at
`/tmp/opencode/architecture-review-20260907-212838.html` (line numbers live
there; this spec and its tickets name functions/modules only, so they don't
rot). Base tree: the hotloops-merged tree (region-merge + Transfer_memo
deletion + the honest stack @ 18df839) with the in-flight directional-infs
edits on disk.

## Problem Statement

The analysis is 100% sound and the gates are green, but the codebase has
accumulated structural debt faster than any single review could retire it:
the same facts are computed twice (the word-ops twin survived its own
substrate migration; three verbatim clones live inside the constraint lane),
dead code from deleted eras is still tracked (Phase-B banner debris, orphan
probes, npm residue in an OCaml tree), per-call loops recompute per-sub
facts, the emitter and the VSA engine each live in one 2000-3000-line file
behind a frozen interface, and the mutable-state census shows ~7 accumulator
refs that are plain folds in disguise. A returning expert spends their
first hour re-deriving which of two identical functions is authoritative,
and the next agent session inherits the same question.

## Solution

A nine-ticket cleanup lane, one battery-verified commit each, that deletes
the dead surface, merges the twins, hoists the repeated per-sub facts behind
named helpers, converts the foldable refs to folds (and records the
deliberate mutation sites as non-candidates so they are never "cleaned"),
and splits the two mega-files along their already-frozen seams. Aggregate
≈ −2,400 LOC with zero intended behavior change: every ticket lands behind
the full battery, with corpus IR byte-identity against the post-region-merge
baseline as the identity oracle.

**⚠ Re-baseline context (from hotloops): region ids renumber corpus-wide
(ascending-in-lo). The IR byte-identity reference is the post-region-merge
emission (`/tmp/opencode/rm1-ref` / `rm1-em2`, 35/35 self-consistent);
pre-region-merge emissions are NOT comparable. Two-run determinism: expect
the known renumbering-only wobble class on gcc-12/cksum_avx2 — diff for
non-renaming residue, not raw inequality.**

## User Stories

1. As a returning expert, I want the word-ops module deleted rather than
   twinned, so that every arithmetic helper has exactly one home to fix.
2. As a returning expert, I want the constraint lane's verbatim twins
   merged, so that the backward-refinement design (one rule per shape) is
   visible in the code instead of duplicated three ways.
3. As a returning expert, I want each of the fission name spellings minted
   by one function, so that the `stack_rN` convention is a fact, not three
   hand-typed strings.
4. As a returning expert, I want the deliberate mutation sites documented
   as non-candidates, so that I never waste an hour deciding whether the
   shared walk-budget cell is "legacy" (it is the binding-regime seam).
5. As an agent session, I want dead code deleted (zero-caller functions,
   orphan probes, ghost doc references, npm residue), so that my greps
   return only live facts and my edits can't target dead code.
6. As an agent session, I want per-sub facts computed once and threaded
   (the FP slot set, the def-fact index, the ABI record), so that I don't
   "rediscover" and re-add a recompute that a previous lane deleted.
7. As an agent session, I want the fold-shaped refs converted to folds,
   so that the remaining `ref` sites are all genuinely mutable state and
   my mutation-census greps mean something.
8. As a test author, I want the fixture vocabulary in its own module
   (harness vs fixtures split), so that adding the next loop family is a
   20-line change, not 80 lines of Blk.Builder scaffolding.
9. As a test author, I want one run-fixpoint-and-extract helper, so that
   the anchored-entry contract is named once and defaults correctly.
10. As an emitter consumer, I want the emitter's implementation split
    behind the already-frozen emission seam, so that I can read the
    FP-intrinsic lane without scrolling the whole call machinery.
11. As an emitter consumer, I want the 26-row FP-intrinsic table pinned
    where it lives (it already is, via the emission wing), so that any
    dedup near it fails loudly if a row is dropped.
12. As a maintainer, I want the VSA engine split along the
    forward-transfer / backward-walk / driver seams, so that the
    trace-partitioning design (ADR-0002) maps onto the file layout.
13. As a maintainer, I want the pass pipeline file split into filter /
    sections / registration, so that each pipeline stage is a readable
    unit matching the pass order.
14. As a maintainer, I want redundant tag lookups removed from the
    per-def emission path, so that the 100%-tagging invariant is expressed
    structurally (the tag is found once and passed).
15. As a reviewer, I want provably-unreachable guards deleted rather than
    kept "for safety", so that a guard that CAN fire is trustworthy.
16. As a reviewer, I want the NEQ-complement row as one named helper, so
    that the two-piece complement (TOP minus a point) is one audited
    implementation.
17. As a reviewer, I want the Kosaraju duplication unified, so that the
    SCC algorithm is audited once for both the block graph and the
    widening-need var graph.
18. As a perf engineer, I want the per-call whole-sub rescans hoisted,
    so that the emitter's cost scales with calls, not calls × defs.
19. As a perf engineer, I want the stack model's def-fact index, so that
    the escape analyses stop re-walking the same defs six ways.
20. As a perf engineer, I want the worklist pop's linear scan measured
    before it is replaced, so that the last O(n²) in the driver dies by
    measurement, not by vibes (the C8 lesson).
21. As a doc reader, I want the ghost references fixed (the seam list
   naming deleted modules, the vsa-usage note), so that following the
   docs compiles.
22. As a doc reader, I want the mangled KB conflict string re-wrapped,
   so that operator-facing errors are readable.
23. As a CI runner, I want every ticket gated on the full battery with
    zero new test seams, so that the lane's cost is the existing gates
    and its proof is the existing gates.
24. As the next perf lane, I want this cleanup to NOT touch behavior,
    so that my producer-wall measurements aren't polluted by a cleanup.
    (The known +80% producer regression vs c46454a is its own lane.)
25. As the determinism diagnosis lane, I want this cleanup to avoid the
    VSA driver's ordering-sensitive machinery, so that my flake
    isolation isn't confounded (the exposed renumbering wobble is
    upstream hash-order, not this code).
26. As a probe user, I want the timing probes' shared shell hoisted, so
    that a new probe is a lens, not a copy-paste of init/load/time.
27. As a probe user, I want misgated probes fixed, so that a default-
    profile build doesn't carry a probe whose headline feature is
    debug-only.
28. As a test-suite reader, I want the shift-semantics families in one
    home, so that the CLP shift contract is found in one place.
29. As a test-suite reader, I want the mixed alias spellings normalized,
    so that one file doesn't use two names for the same module.
30. As a stakeholder, I want the battery green at every commit, so that
    any ticket can be reverted independently if a gate disagrees.

## Implementation Decisions

- **Lens 1 — Deletions (17).** Zero-caller-verified dead code only:
  the `Cbat_word_ops` twin module (its whole op set now lives inside the
  word substrate; migrate `is_one`/`half`/`gt_int`/`endian_string` call
  sites and the open in `cbat_clp`, keep the referee as the oracle); the
  tautological tag guard + its unreachable invariant arm in the emitter;
  `jmp_target`, `kind_lo`, `lt_int`, `of_int32`, `canonize`; the identity
  map in the extraction walk; ~70 lines of Phase-B banner debris; the
  dead SMT artifact; npm tool residue; the orphaned/unbuildable probe;
  the dead half of the operand census probe; `StrMap`/`requires` in the
  pipeline file; four unused module aliases in the VSA pass; the eight
  freshly-orphaned ABI exports (the one with a live consumer stays).
- **Lens 2 — Removals (11).** Inline re-derivations of existing facts
  (the positive-kind predicate, the precise-model predicate, the local
  Hashtbl alias); pass-through wrappers in DCE; the ABI getter that
  re-projects what the emit context already carries; the substrate-migration
  word-conversion shims at the frame constants; the double module alias
  and duplicate opens in the fixture module; mixed qualified/alias
  spellings within one test file; the mangled conflict-printer literal;
  the dead `is_main` disjunct; unused parameters on the .text loader and
  sub emitter; the nested-dir probe outlier (owner decision).
- **Lens 3 — Merges (19).** The three verbatim twins in the backward
  constraint lane (the bounds→CLP constructor appearing under two names;
  the HIGH-cast pre-image duplicated between the walk and the leaf-constraint
  extractor; the LSHIFT pre-image duplicated between the meeting and the
  pairing variants); the NEQ-complement row built four times; the const-
  left/const-right mirror arms of the guard decomposition; the widening-
  need Kosaraju vs the WTO module's own (functorize over the key type);
  the word-meet triple; the unsat-observer twin arms; the emitter's FP-
  lane internal clones (the width-or-default closure ×3, the bitcast
  closure ×3, the trunc/zext coercion ×3, the ret list fetched twice);
  the function-declaration duplicating the ret/arg type builders and the
  registration; the const-address load/store twins and the double
  section scan; the three call-finishing tails; the frame geometry
  triple fragmentation; the mem-marker Load/Store twins; the region-
  builder's two full-sub walks; the regression twin fixtures' residue;
  the shift-family test consolidation; the landmark fixture triple-runs;
  the stack-to-locals duplicate Range arms; the pipeline's triple
  section enumeration; the memory-shape predicate's dead accumulator
  arm and its three repo implementations.
- **Lens 4 — Hoisting (13).** The per-callsite whole-sub scans (the FP
  cast-source width fold, the libm membership lists, the per-arg block
  scans) computed once per sub; the tag found once and passed to the
  memory-access dispatcher; the magic strings (the indirect-call tid,
  the marker names, the intrinsic interface prefix, the trap, the
  region-alloca name) hoisted to named constants at their owners; the
  signature rank's per-var ABI projection; the stack-model def-fact
  index feeding all six consumers; the stack-to-locals ABI resolve
  out of the per-def helper; the worklist pop's linear scan (measure
  first); the frame constants; the probe timing shell; the two corpus
  watcher shells; the run-fixpoint idiom; the misgated stages probe;
  the region-alloca name into the model.
- **Lens 5 — New helpers (12).** The NEQ complement; the word-refine
  discipline; the region alloca name; the FP trio (width-or-default,
  bitcast, width-coerce); the call finisher + extracted-ret binder; the
  const load/store pair; the emitter env reader for the context-get
  pairs; the run-context record-update helpers; the shared has-mem-node
  predicate; the test exit-blocks; the anchored run helper; the generic
  SCC functor.
- **Lens 6 — Ref → fold conversions (8).** The foldable accumulator refs:
  the KB map-join's base/conflict pair (fold keeping the first conflict);
  the VSA pass's tag map (the per-sub computation is pure — plain
  Seq.fold BEFORE the KB write, deleting the monad-iter-plus-ref shape);
  the DCE load-mem collector (the pure visitor-accumulator pattern the
  stack model already uses); the frame-geometry triple max (one fold
  returning the triple, riding the frame-geometry merge); the two
  byte-assembly for-loops (fold over the index range; hot loops, so
  verify neutrality); the Kosaraju block's six refs (die inside the
  generic-SCC merge); the KB read escape (keep, but document as the
  monad-escape idiom); and the keep-list itself — the deliberate
  mutation sites (worklists, fixpoint loops, library-callback closures,
  debug counters, the shared budget cell, the emitter context refs)
  recorded as never-convert.
- **Lens 7 — File splits (12).** The VSA engine split into
  forward-transfer / backward-walk / driver by moving internals OUT to
  the unwrapped domain library first (the proven run-context pattern;
  the wrapped main module re-exports the seam, mli unchanged); the
  emitter split behind its frozen 12-val seam (env/section/exp/fp/core,
  include-chain, zero dune changes); the CLP split
  (types+creation+order+lattice vs arithmetic); the pipeline file split
  (filter/sections/registration); the fixture module split (harness vs
  fixtures); the domain-property move out of the regression file; the
  memmap Key module out; the landmark fixtures home; the nested probe
  dir; the shared-vocabulary split of convutils; the ADR-recorded
  non-split (the contextual Dep wrapper stays, per its ADR); the probe
  dune-stanza consolidation question.
- **Ordering.** Nine tickets, one battery-verified commit each: dead
  code first (shrinks every later diff), the twin second (referee-
  gated), pass-throughs/hoists third, the constraint-lane merges fourth,
  ref→fold fifth, emitter dedup sixth, stack model seventh, tests
  eighth, splits last (contents stabilize before files move).
- **Non-candidates (updated for hotloops).** The region merge loop is
  DONE (region-merge replaced it with sort-and-sweep and renumbered the
  ids — that re-baseline is inherited, not re-litigated); the assoc-list
  last-wins rule, the degraded-sub region recompute, the SP-value vs
  SP-reference predicate pair, the FP table's "duplicate-looking" rows,
  the corpus sources, the reference papers, the dune cppo mirror, and
  the debug-no-op stubs stay as they are, by recorded decision.

## Testing Decisions

- **Battery-only, zero new seams (owner-settled).** No ticket adds a
  test seam; the existing surfaces are the proof.
- The unit suite (plain-OCaml checker, direct-exe run for the honest
  count) gates every ticket: 0 FAIL. Domain/substrate items are
  additionally covered by the differential referee stanza (the clpequiv
  2.86M-check sweep) already wired into runtest — that stanza is the
  oracle for the word-ops twin merge.
- Corpus emission 35/35 rc=0 with **IR byte-identity vs the
  post-region-merge baseline** for every behavior-identical ticket; the
  known two-run renumbering wobble (gcc-12/cksum_avx2 class) is diffed
  for non-renaming residue, not raw inequality.
- check_allocas (expect the pre-existing 3 shape-d fails on the real
  PIE binaries — identical to control), the full semantic suite, and
  the optimization-safety gate (subsumed by byte-identity where IR is
  unchanged).
- A good test here asserts external behavior only: the suite's
  value-exact pins (the F1/L3 families, the R12 sweep fixtures, the
  73-check emission wing) are what make merges of twins safe — they
  pin values, not call shapes. Test refactors must preserve check
  names/counts byte-for-byte (output-diff the suite).
- Prior art: the honest-gate's direct-exe count discipline; the
  region-merge lane's two-run determinism harness; the emission wing's
  textual-IR asserts; the fixture-lib lane's zero-check-moved
  relocation proof.

## Out of Scope

- Any behavior change (soundness, precision, tags, IR) — this is a
  cleanup lane; a candidate that moves a tag or a byte goes back to
  grilling, not into a commit.
- The +80% producer wall regression vs the older control — its own
  perf lane.
- The exposed fixpoint determinism flake — its own diagnosis ticket
  (upstream hash-order class; this lane must not touch the driver's
  ordering-sensitive machinery).
- Re-litigating the region-id renumbering or byte-comparing against
  pre-region-merge emissions.
- The 2026-09-02 recorded dead-by-measurement items (the static def
  table per ADR-0006, the shape_of_addr last-wins, the stl recompute,
  Sub.to_graph consolidation).
- Probe deletion beyond the two owner-decision items (the probe
  culture keeps closed-investigation instruments as templates).

## Further Notes

- Per-candidate evidence with file:line (re-verified against the
  hotloops tree + in-flight edits): the architecture review HTML
  (appendix above). Line numbers rot; the spec names functions.
- The 92 candidates break down 17 deletions / 11 removals / 19 merges /
  13 hoists / 12 helpers / 8 ref→fold / 12 splits; several ref→fold
  items ride their natural merge tickets (the Kosaraju refs inside the
  generic-SCC merge; the frame-geometry refs inside the geometry merge).
- Tickets: `01-dead-code.md`, `02-word-ops-twin.md`,
  `03-passthroughs-hoists.md`, `04-constraint-lane-merges.md`,
  `05-ref-to-fold.md`, `06-emitter-dedup.md`, `07-stack-model.md`,
  `08-tests.md`, `09-file-splits.md` — same dir.
- The walk-budget cell, the memo/stages counters, the worklist state,
  and the emit-context refs are load-bearing mutable state. They are
  listed in ticket 05's keep-list precisely so a future "remove all
  refs" pass cannot land them.
