# T13 — the jump-compiler pass: jcc idioms become value comparisons, once (P1)

Owner directive (2026-09-11): "What if we create a new BAP pass that
simplifies jump conditions to actual value comparisons? That way we
decouple, increase optimizability of LLVM code, and have cleaner code
in the VSA pass. I.e. remove jcc completely!"
Spec: `.scratch/typed-model/spec.md` (binding constraints + the
architecture-side doctrine apply).
Blocked-by: **T10** (the pipeline structure it extends).
Blocks: **T5** (the SSE lane's guard rows shrink to the comparison
core — T5 should branch after this lane, not before).
Related: T12 (the kind collapse — independent, may interleave);
the T8-repaired acquisition probe lives in the layer this lane
shrinks.

## The problem (the coupling today)

A lifted conditional jump is a FLAGS IDIOM: `ZF := (a-b) == 0;
jmp ~if ZF ...` (and the unsigned/signed families through CF/OF/SF —
`jae` = `not CF`, `jg` = `~ZF & ~(OF xor SF)`, ...). The VSA's jump
compiler — `decoded_condition`, `decoder_constraint`'s rows, the
complement table, the polarity-aware acquisition probe — decodes these
idioms INSIDE the analysis, per query, forever. The emitter
separately translates the flag defs into computations. The same
semantic knowledge (per-flag-setting-opcode flag effects) exists in
two places, and the consumer's optimizer never sees a plain `icmp`.

## What lands

A NEW BAP pass (first in the analysis chain, after hike-filter):
compile every jump condition to an ACTUAL VALUE COMPARISON.

- The pass holds the flag-semantics knowledge ONCE (per
  flag-setting-opcode effects; the same facts the VSA's decoder rows
  encode today) and REWRITES the BIR: a conditional jump whose cond
  resolves through a DOMINATING SINGLE flag def becomes
  `jmp ~cond=((a-b) == 0)`-style value comparison; the flag defs the
  rewrite consumes die; no jcc idiom survives where the rewrite fires.
- The rule is total over proven cases and the identity elsewhere: a
  cond with no dominating single flag def (flags live across blocks;
  partial-flag effects) keeps the current path — the identity, not a
  refusal. The pass DELETES the idioms it compiles; the case-count
  delta is the acceptance's first row.
- The VSA's guard layer SHRINKS to the comparison core: the decoder's
  flag-idiom rows, the complement table's flag arms, and the
  acquisition probe's flag-idiom handling are deleted (the T8-repaired
  polarity rule simplifies to the comparison-level truth it always
  pointed at). What remains: comparison constraints + the landmark
  machinery (unchanged semantics, cleaner input).
- The emitter: branches emit `icmp` + `br` on the comparison directly —
  the consumer's optimizer sees native comparisons (the
  optimizability prize); the flag defs no longer exist to translate.

## The measured class

The -O0 corpus's conditional jumps (census in the verdict: how many
jcc idioms compile, how many residuals stay, per idiom family). The
landmark pins (F1, green since T8) are the feature's acceptance:
they must STAY green with the cleaner input (their fixtures' jne
counters compile to comparisons; the landmarks must still fire — the
 pins' text already describes value-comparison semantics).

## Binding constraints

NO GATES, NO FALLBACKS, one mechanism, architecture-side fixes (the
diff deletes the decoder rows it obsoletes), conversion-first
(inventoried reds). Byte-identity is NOT the acceptance (the BIR and
the emitted IR both change deliberately); the semantic gates are the
oracle.

## Battery protocol (you hold the shared plugin slot)

`eval $(opam env)` first; `record_provenance.sh` after every install;
battery artifacts on home disk (`/home/tovpr/tm-battery/t13/`). Gates
every iteration: `dune runtest` (the suite is FULLY GREEN since T8 —
keep it green; the landmark pins are your feature test), emission
rc=0 both lanes, `unmapped intrinsic` grep clean, check_allocas,
strict -O0 semantics ALL PASS, strict opt-safety ALL PASS or
inventoried, the pinned -O2 gate (attribution-only movement),
convergence rows vs the pre-T13 reference — the optimizability prize
is THIS ticket's number: post-opt instruction counts on
branch-heavy sources should DROP (report per-source).

## Acceptance

- The pass exists, registered in the pipeline (after hike-filter);
  the jcc flag-idiom census: compiled vs residual, per family.
- The VSA's decoder shrinks (the deleted rows listed); the emitter
  emits icmp on compiled branches; grep-clean of the deleted arms.
- All gates green or inventoried; the F1 pins green; the
  optimizability movement reported per source.
- Verdict: the pass's rule (the flag-effects table, the dominance
  condition), the census, the deleted-case inventory, the gate table,
  the pin with attribution, the convergence/optimizability rows.

Worktree: `/home/tovpr/hike-t13`, branch `tm/t13-jump-compiler`.
