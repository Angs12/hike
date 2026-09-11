# T13 construction verdict — the jump compiler (the BIR-level pass + its pins)

Lane `tm/t13-jump-compiler`, worktree `/home/tovpr/hike-t13`. Authority:
`T13-jump-compiler-pass.md` (the redesign-not-relocate mandate, the five
priority rules, the identity residual). This session = the PASS ITSELF
(ON THE BIR LEVEL) + its unit pins, DUNE-LOCAL ONLY: pipeline
registration, the VSA decoder shrink, and the battery are the
slot-window phase (the ticket's own protocol). No `dune install`, no
`bap` — the shared plugin slot was untouched.

## What landed

- `src/hike_jump.ml[i]` — `Hike.Jump` (`compile_sub`, `compile_program`),
  a BIR→BIR term transformation over sub terms. Traversal via the term
  mapper combinators (`Term.map blk_t` / `Term.map jmp_t` /
  `Term.filter def_t`); fact extraction is single-node kind tests over
  one rhs at a time (sanctioned). The flag semantics lives HERE ONCE —
  the def-side twin of `cbat_walk`'s decoder rows.
- `src/hike.ml[i]` — the `Hike.Jump` re-export (+ `family_of_cond`, the
  census probe's label).
- `zz_scratch_probe/jump_census.ml[i]` — the census instrument (dune
  exec; per-family compiled/residual with binary+sub attribution).
- `test_cbat/test_jump.ml` — 34 pins (inventory below).

## The flag-effects table (consolidated; verified against bir_dump)

Ground truth: `zz_scratch_probe/bir_dump.ml` over the -O0 corpus
(37 PIE bins). The lifter emits the FULL x86 flag group after every
flag-setting op — `CF/OF/AF/PF/SF/ZF` — and the ten jcc families read
only `ZF/CF/SF/OF` (AF/PF are ignored; no family decodes them).

| opcode | the lifted flag defs (real shapes) | consumed? |
|---|---|---|
| **sub/cmp** (`d := a − b`) | `CF := a < b` (LT = the borrow) · `OF := high:1[(a^b) & (a^d)]` · `SF := high:1[d]` · `ZF := 0 = d` | all (the jcc universe) |
| **add** (`d := a + b`) | `CF := d < a` (LT = the carry) · `OF := high:1[~sg(a) & (sg(a) \| sg(b)) & ~(sg(a)&sg(b))]`-form (`high:1[#a] = ...` in dump order) · `SF := high:1[d]` · `ZF := 0 = d` | CF **shape-honestly** (the LT fact IS the carry: `d <u a`), SF/ZF; add-OF not consumed (not the sub shape) |
| **logic / test** (`d := a & b`) | `CF := 0` · `OF := 0` (literal consts for register operands; for a memory operand the lifter emits the constant-false `a <u 0` and the and-shape `OF := high:1[a & (a^d)]`) · `SF := high:1[d]` · `ZF := 0 = d` | CF/OF consts, SF, ZF; the and-shape OF is NOT consumed (see residual r1) |
| **neg** | `CF := (a <> 0)` (NEQ) · rest as sub | NOT consumed (the NEQ-shaped CF row is a possible future row; 40 corpus defs, zero jb over them) |
| **shifts** | `CF := high:1[#t << k]` · `OF := unknown[bits]` (variable shifts) · `SF/ZF` as usual | CF/OF NOT consumed (the carry shape is not a comparison); SF/ZF consumed |
| **inc/dec** | the group WITHOUT a CF def (CF preserved by the isa) | SF/ZF/OF families compile; **CF families stay the identity** (a per-block facts regime cannot see the preserved CF — the sound answer) |
| **imul** | TWO OF defs (the `<>` partial form then the and-form) | OF not consumed → signed families over imul stay the identity |

Corpus-wide shape census (defs, not conds): ZF is ALWAYS `0 = <exp>`
(zero-LEFT — `extract_facts` handles both arms; 1531 defs) + 111 consts
+ 42 `unknown[bits]`; CF: LT 1072, const-0 329, shift 241, NEQ 40,
unknown 2.

## The rewrite rules as landed (the five priority rules)

1. **REUSE** — the zero family compares the flag def's own operand: a
   var `d` reuses the var (`tmp := i−k; ZF := (0 = tmp); jne` →
   `cond = (tmp != 0)`, never `(i−k) != 0` re-emitted). The inline
   guard: every var the re-emitted comparison reads must have its last
   def at-or-before the producing flag def's position (the re-emission
   at the jump reads the values the flag defs read).
2. **FOLD** — `a−a` → the constant cond; `x−0` → `x` (the cmp x,0
   shape); `(x−y) = 0` → `x = y`; the test conjunction is kept
   (`(x&y) = 0`); constant ZF facts (`ZF := 1/0`) fold the cond to the
   constant.
3. **WIDTH-MINIMAL** — the comparison rides the inlined exps' own
   width; the zero constant is minted at that width (a 32-bit sub gives
   a 32-bit comparison; pinned).
4. **CANONICALIZE** — complement rows FLIP THE OPERANDS, never wrap in
   NOT (`jae` = `b <=u a`, `jge` = `y <=s x`, `ja` = `y <u x`,
   `jg` = `y <s x`); the lifter's constant-left `0 = d` normalizes to
   constant-right `(d == 0)`; identical conds for jumps over the same
   def (CSE-friendly). The MINUS fold keeps minuend-left — constant-
   right for every realizable cmp shape (the immediate is always the
   subtrahend).
5. **DROP** — every def of a consumed flag var whose var is unused
   sub-wide after the rewrite (`uses_of` = defs' rhs + jmps + phis).
   With multiple defs of the flag in the block, all of them die (the
   var is unused — every def of it is dead).

## The dominance condition (as landed)

Block-local facts, one predicate: each flag a family consumes must have
a def in the JUMP'S OWN BLOCK, and the facts come from that block's
**single reaching def** — the LAST def of the flag var (all BIR defs
precede all jmps, so every cond in the block reads the last one;
earlier flag defs are dead writes). Everything else keeps the current
path UNCHANGED (the identity, never a refusal):

- flags defined only in predecessor blocks (flags live across blocks);
- a flag whose reaching def has an unknown rhs (`unknown[bits]`, shift
  carries, neg-NEQ, the and-OF shape);
- cross-flag inconsistency: the collapse rows (JBE/JA = `CF|ZF`, and
  the signed rows) hold only when the consumed facts refer to the SAME
  subtraction (`is_minus_xy` + `same_exp`); facts from different
  instructions stay the identity — that is the complete rule for that
  shape, not a gate (the collapse without the shared subtraction is
  UNSOUND, so the identity is the sound answer);
- the inline guard failing (an intervening redefinition).

Construction fix landed this session: the committed fold had a
**parity accident** — it removed a flag var on its second def and
re-set it on the third, so an ODD def count compiled from the last def
while an EVEN count went residual. Sound either way, but not the
mandate's rule; it is now uniform single-REACHING-def (last-def-wins).
This converted the corpus's biggest residual class (the crt `_init`
`sub rsp,8` + `test` pairs: 43 je residuals → 0).

## The census (the acceptance's first row; `/tmp/corpus`, 37 bins)

`dune exec zz_scratch_probe/jump_census.exe -- /tmp/corpus/*` (dune-local;
the pass is NOT registered, so this is compile_sub applied per sub in
the probe):

| family | compiled | residual |
|---|---|---|
| je | 238 | 0 |
| jne | 66 | 0 |
| jle | 28 | 1 |
| jl | 10 | 0 |
| ja | 9 | 0 |
| jg | 6 | 0 |
| jb | 3 | 0 |
| jbe | 1 | 0 |
| jae | 1 | 0 |
| jge | 0 | 0 |
| **total** | **362** | **1** (99.7%) |

Plus: 28 non-idiom conds — ALREADY value comparisons (the va_arg
alignment checks `(RBP − 0xN & 0xF) = 0`, `#t = 0` forms, the FP
intrinsic select/let conds) — the form the pass wants everything to
have; and 1654 unconditional jumps (cond = 1, untouched).

The one residual (r1): `rec_struct :: build` — a `jle` whose flag group
is a test/and over a MEMORY operand: ZF/SF consumed shapes are present,
but the reaching OF def is the and-shape `high:1[a & (a^d)]`, which is
not provably the sub-overflow predicate — the OF fact stays absent and
the signed family keeps the identity. Sound; the je over the same
group's ZF compiled. This is the table's documented test/and row
boundary, not a miss (consuming it would require relating `d` to
`a & b` through the store — a future row if a corpus class demands it).

bir_dump evidence per family (ground-truth shapes the table was checked
against): `factorial` (the loop's `cmp/jae` → `goto X if ~CF`, the
flag group exactly as the table's sub row, imul's TWO OF defs after the
multiply), `register_tm_clones` (five flag groups in ONE block, the
cond reading the last: the reaching-def rule's real shape; `test rax,rax`
with literal `CF := 0; OF := 0`), `rec_struct build` (the memory-operand
test/and group, r1), `fizzbuzz`/`deep_recursion` (the jle/jg xor-core
conds; `CF := 0` logic rows; shift carries), corpus-wide (`CF := 0` ×329,
NEQ-CF ×40 = neg, shift-CF ×241 — none consumed).

## The pin inventory (34, `test_cbat/test_jump.ml`)

- Families, exact-structural-equality conds: jz → `x = y` (fold, inline
  diff); jne → `t != 0` (REUSE — the counter-loop shape, the tmp def
  survives); jb → `x <u y`; jb over add-carry → `t <u x` (the carry
  verbatim, the sum def survives); jae → `y <=u x` (complement flips,
  no NOT); jbe → `x <=u y` (consumes CF+ZF); ja → `y <u x`; jl →
  `x <s y`; jle → `x <=s y`; jg → `y <s x`; jge → `y <=s x`.
- Drops: jz/jne/jb(+add)/jbe consumed flag defs die; the reused tmp/sum
  defs survive.
- Folds: test jz → `(x&y) = 0`; cmp x,0 jnz → `x != 0`; a−a jz → `1`.
- WIDTH: a 32-bit cmp gives a 32-bit comparison (`x32 = y32`).
- CFG: both jmps of a block compile; block/target structure unchanged.
- Residual identities: cross-block flags (cond + def untouched);
  unknown opcode (PF:unknown); inconsistent jbe (ZF's d is not CF's
  subtraction); inc/dec CF-preserved (no CF def in the block — jbe the
  identity, defs untouched); unconditional (cond = 1) untouched with
  all defs.
- The reaching def: two ZF defs → the cond compiles from the LAST def
  (`y = 0`) and BOTH defs die (the var unused).

Fixture grammar per AGENTS.md: real block tids (targets built first,
`Term.tid` used), cond-Goto jmps through `Blk.Builder`, no dangling
tids. These fixtures feed ONLY the jump compiler (no emitter), so the
cond-Goto + fallthrough-Goto pairing is not exercised here.

## Validation (dune-local)

| gate | result |
|---|---|
| `dune build` (default profile) | rc=0 ✅ |
| `dune runtest --force` | **ALL CBAT TESTS PASSED**, rc=0; 34/34 t13 pins ✅ |
| referee (`clpequiv`, the test stanza) | **2,861,148 checks / 0 mismatches** ✅ |
| suite movement | nothing else moved (the 8 pre-existing E2eD/LM pins behave as recorded — owner triage) ✅ |

No `dune install`, no `bap`, no battery — per the lane protocol.

## Case-count projection (what the VSA decoder sheds at wire-up)

After registration (hike-jump FIRST, after hike-filter), a rewritten
cond is a Bil comparison (`EQ/NEQ/LT/LE/SLT/SLE` over value exps) — the
VSA's flag-idiom machinery becomes dead ON COMPILED INPUT:

- `decoded_condition` (cbat_walk.ml:24): all five structural flag rows
  (`ZF` → EQ, `~ZF` → NEQ, the xor-core → SLT, `ZF|core` → SLE,
  `~(CF|ZF)` → UGT) stop matching — the corpus's 351 je/jne/jl/jle/ja
  conds carried exactly those shapes. The other 11 (jb/jae/jbe/jg)
  decoded only through the fallthrough-polarity arm
  (`complement_guard_op` at the `assume_jump_cond_with_group` call
  site, with the T8 NEQ special-case) — no flag conds remain to route
  through it.
- `complement_guard_op`'s flag arms survive ONLY as
  `complement_binop_guard` over comparisons (the false edge of a
  comparison still needs the complement — the comparison core's own
  table, 10 rows, unchanged semantics).
- The T8-repaired acquisition polarity (the `Some NEQ -> gop` rule)
  loses its jcc-NOT input: compiled jne's are literal `NEQ` comparisons
  — the polarity fact the probe recovered by decoding the flag idiom is
  then the comparison-level truth it always pointed at.
- What REMAINS live and feeds the refinement:
  `comparison_constraint`'s rows (LT/LE/EQ/SLT/SLE + NEQ identity) +
  the landmark machinery (unchanged). The F1 pins' jne-counter fixtures
  compile their `~ZF` to `t != 0` and must stay green at wire-up — the
  ticket's feature acceptance.
- The emitter (deferred): flag defs no longer exist to translate on
  compiled paths; branches emit `icmp` + `br` directly — the
  optimizability prize (post-opt counts on branch-heavy sources) is the
  wire-up battery's number, reported then.

Projected per-corpus movement: 362 conds/corpus switch from the
flag-idiom decode path to the comparison core; 28 already-comparison
conds are unchanged; 1 residual (r1) keeps today's path.

## DEFERRED (the slot-window phase)

1. Pipeline registration (`hike-jump` after `hike-filter`; pass deps).
2. The VSA decoder shrink (delete the rows above; grep-clean proof).
3. The emitter's icmp+br on compiled branches; the flag-def translation
   arms dying.
4. The battery (both corpora, strict semantics, strict opt-safety, the
   pinned -O2 gate, convergence rows, the optimizability movement
   per source, `record_provenance.sh`).
5. Possible future rows (documented, not built): the neg-NEQ CF row
   (`jb` = `a != 0`; 40 corpus defs, no conds over them today); the
   and-shape OF (r1) if a class demands it; `and $-16,%rsp`-shaped
   alignment conds are ALREADY value comparisons in the lift (no row
   needed — census-verified).

## Commits

- `6341a3d` the pass core (the flag-effects table + the BIR rewrite)
- `284973e` the unit pins (v1, 28 checks)
- `eb8c49b` the census instrument (`family_of_cond` + jump_census)
- `781902a` the single REACHING def (the parity fix; consumed vars drop
  whole; pins 31)
- (this commit) the add-carry pin (34) + the verdict
