# T10 — the pipeline simplification: intrinsic callers lift; the record rides the term (P1)

Owner directives (2026-09-11): "why does the intrinsic callers filter
exist? We can now handle them." And: "instead of vsa_info on a map on
KB — just tag the Term SUB directly, using a tag."
Spec: `.scratch/typed-model/spec.md` (binding constraints + the
architecture-side doctrine apply).
Blocked-by: nothing (S10b's split lands first only to avoid conflicts).
Blocks: nothing; the corpus re-baseline feeds T5's measured scope.

## Part 1 — the intrinsic-callers filter dies

`hike-filter`'s exclusion of subs that CALL intrinsic subs is a relic
of the incomplete-FP-table era (the 2026-09-02 incident class: 11 of
26 `native_fp_op` rows silently dropped — the emission wing now pins
the 26-row table, and `fp_op_inputs` makes the mapped name THE
interface fact). The promotion, thunks, and window lanes are
callee-agnostic. What stays filtered: the intrinsic SUBS themselves
(BAP `@intrinsic:*` placeholders are not code — call TARGETS map
through the table; the placeholder subs are never lifted).

- Remove the intrinsic-callers exclusion (and the intrinsic-callers
  arm of the symbol-table check if it exists only to serve it).
- Deliberate re-baseline: more subs lifted corpus-wide; the emission
  and diagnostic sets change; the battery's semantic gates are the
  oracle. Grep the emissions for `unmapped intrinsic` (the 09-02
  gotcha) as an explicit gate.

## Part 2 — THE EMITTER CONSUMES NO RECORD AT ALL (owner directive,
## strengthened)

"I also believe that the emitter should not access vsa_info per sub
AT ALL." This subordinates and strengthens the carrier question. The
construction, in doctrine order:

1. **The promotion becomes a BIR REWRITE** (the mem-fission/DCE
   precedent — pass-level term transformation, not emitter record
   reading): the callee's proven incoming-slot loads become reads of
   REAL BIR SUB PARAMETERS (the sub term gains them); the caller's
   outgoing stores become the CALL JMP's ARGUMENTS (structurally, on
   the call term); singleton-resolved indirect targets become DIRECT
   BIR call targets. The emitter then TRANSCRIBES structure that is
   already there — params are params, args are args — and needs no
   record to know any of it.
2. **Per-def facts stay on defs**: the kind tag (the 100% Tagging
   Invariant), the VLA marker, the frame-wrap license — all per-def,
   never per-sub queries.
3. **Geometry travels as a narrow layout fact** (frame size, region
   sizes/bytes — the alloca construction inputs): a small standalone
   per-sub LAYOUT tag (NOT vsa_info — no analysis facts in it), or the
   equally-structural alternative the implementer justified. The
   regions themselves already travel by the name convention
   (`stack_rN` / `stack_rN_base`).
4. **The record's carrier is then the pipeline's business only**
   (hike-vsa -> the model -> STL): whether it stays a KB map or moves
   to a term tag (the owner's earlier lean) is decided by what the
   post-rewrite consumers need — the emitter reads NONE of it. If the
   emitter is the record's last consumer, the KB-vs-tag question may
   dissolve entirely; verify and report.

Grep-clean acceptance: ZERO `vsa_info`/record reads in the bil2llvm*
modules (the emitter); `Hike_kb.info_of_sub` either gone or
pipeline-only (no emitter path reaches it — prove by the module
dependency direction + grep).

## Binding constraints

NO GATES, NO FALLBACKS, one mechanism, architecture-side fixes,
conversion-first (failures inventoried). Byte-identity is NOT an
acceptance (both parts change the lifted surface deliberately); the
semantic gates are the oracle: strict -O0 semantics 37/37 on the
(possibly larger) corpus, strict opt-safety all PASS or inventoried,
the pinned -O2 gate (the set may only change by attribution, recorded),
referee 2,861,148/0, runtest == the 8 baseline + named inventory,
both profiles build.

## Battery protocol (you hold the shared plugin slot)

`eval $(opam env)` first; `record_provenance.sh` after every install;
battery artifacts on home disk (`/home/tovpr/tm-battery/t10/`).
Corpus: rebuild BOTH lanes with the new sources' callers unfiltered —
INTO YOUR OWN DIRS (`/home/tovpr/tm-battery/t10/corpus*`), never
`/tmp` (the recorded deviation stays a one-off; the battery's corpora
switch when you land).

Gates every iteration: `dune runtest`, both-lane emission rc=0 +
`unmapped intrinsic` grep clean, check_allocas, strict -O0 semantics
ALL PASS, strict opt-safety ALL PASS or inventoried, the pinned gate
vs `scripts/semantic/o2_known_failures.txt` (attribution only — new
attribution entries recorded per binary, growth blocks), convergence
vs the pre-T10 reference with every moved row reported.

## Acceptance

- The intrinsic-callers exclusion is GONE (grep-clean); intrinsic
  subs stay excluded.
- The KB side table for the record is GONE (grep-clean); the record
  rides the term; one carrier.
- The corpus re-baseline itemized (subs gained, emissions changed,
  diagnostics changed); all semantic gates green or inventoried.
- Verdict: per-part mechanism, the encoding decision (with the BAP
  constraint facts), the gate table, the re-measured pin with
  attribution, the convergence rows.

Worktree: `/home/tovpr/hike-t10`, branch `tm/t10-pipeline`.
