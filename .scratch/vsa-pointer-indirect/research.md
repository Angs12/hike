# Research: tagging pointer-indirect stack accesses (the va_list class)

Status: research complete; no production code changed. The scratch probe
`zz_scratch_probe/vsa_ptr_diag.ml` (+ its dune stanza) was added for this
investigation — scratch-only, never installed, following the `audit02`
pattern. The background-research-agent path failed twice (provider rate
limit, then transport error), so this was researched inline.

Question: how can the VSA be improved so `mem[RAX]` — where `RAX` holds an
SP-derived pointer stored into a frame cell and loaded back — is classified
as a stack access with a POSITIVE offset range, making `is_positive_kind`
fire, the `hike_stack` param granted, and the emission anchored on the
caller's arg area?

## 1. Problem statement (machine-verified)

Two corpus binaries fail the semantic gate only through this class:

- `/tmp/corpus/variadic`, callee `sum_n(count, ...)`: lifted prints
  `sum = -883326090` (native 280). The 6 register varargs are summed
  correctly; the single stack-spilled 7th arg reads garbage.
- `/tmp/corpus/va_arg_vacopy`, callee `two_pass(count, ...)`: prints
  `1 2 3 4 5 0` vs `1 2 3 4 5 6` — again only the stack-spilled arg.

The BIL shape (both binaries; `bap --dump=bil`):

```
RAX := RBP + 0x10                     (* overflow_arg_area — points ABOVE
                                          the callee frame top, into the
                                          caller's outgoing stack-arg area *)
mem := mem with [RBP - 0xC8, el]:u64 <- RAX        (* store into va_list cell *)
... loop ...
RAX := mem[RBP - 0xC8, el]:u64        (* load the pointer back *)
RAX := pad:64[mem[RAX, el]:u32]       (* the va_arg deref — POINTER-INDIRECT *)
RDX := RAX + 8
mem := mem with [RBP - 0xC8, el]:u64 <- RDX        (* advance; loop-carried *)
```

`va_copy` (vacopy only) is inlined as 4×movq whose DESTINATION addresses
also go through registers (`RCX := RBP−0xE0; mem[RCX+8] <- RDX` — a second
pointer-indirect instance inside the same sub).

Emission today: no tag on the deref → `compute_sub_sig`'s `has_positive`
never fires (`src/hike.ml:154-168`) → no `hike_stack` param → the emitter
builds the overflow pointer from the callee's own anchor
(`%631 = add i64 %614, 16`, `%614 = anchor-8`) → the read lands outside any
initialized memory. The contrast that works: `/tmp/corpus/many_args` callee
`sum12` reads stack args DIRECTLY (`mem[RSP+8]`-shaped), gets tags
`Range(16,16)…Range(48,48)`, `hike_stack` is granted, its reads emit
`%52 = add i64 %hike_stack, 8; inttoptr; load` — byte-correct.

Repro / evidence commands:

```
dune exec zz_scratch_probe/vsa_ptr_diag.exe -- /tmp/corpus/variadic sum_n
dune exec zz_scratch_probe/vsa_ptr_diag.exe -- /tmp/corpus/va_arg_vacopy two_pass
```

Probe output (the decisive rows):

```
DEF %000007fe: pad:64[mem[RAX, el]:u32]
  addr=RAX rewritten=false ch1=false ch2=false({0..0xFFFFFFFFFFFFFFF8}^inf) tag=(untagged)

two_pass:
DEF %0000093c: pad:64[mem[RAX, el]:u32]
  addr=RAX rewritten=false ch1=false ch2=false({0..0xFFFFFFFFFFFFFFF8}^inf) tag=(untagged)
DEF %00000bbb: pad:64[mem[RAX, el]:u32]
  addr=RAX rewritten=false ch1=false ch2=false(TOP) tag=(untagged)
```

(Anchored coordinates: entry SP = 0, so `RBP = -8` after the rbp push, the
va_list cells sit at −0xD0…−0xB4, and the overflow pointer's initial value
is `RBP+0x10 = +8` — POSITIVE: the caller's arg area.)

## 2. Where the value is lost on today's tree

The T02-era symptom (`hike: guarded: Unbounded`) is GONE — `audit02.exe`
on today's tree reports `Unbounded(PROD)=0` for both subs. The restriction
removal (ADR-0003) landed Channel 2 precisely for this "saved-address
class": a stack address stored to a cell and reloaded. The loss is now
DOWNSTREAM of Channel 2's admission rule, in three stacked steps:

**Step 1 — the store-side value is precise.** At `mem[RBP−0xC8] <- RAX`
where `RAX := RBP + 0x10`, `rewrite_addr` (cbat_vsa.ml:284) resolves
`RBP+0x10` via the frame relation to the anchored constant `Int(+8)`;
`denote_def` (cbat_vsa.ml:375) rewrites and denotes, so the cell at key
−208 receives the singleton `{+8}`. Channel 2 works HERE: the
direct-address stores/loads of the va_list fields all tag
(`Range(-216,-216)` etc. in the probe output). The value enters memory
precisely.

**Step 2 — the loop widening destroys it.** The overflow cell is
loop-carried: `{8}` at init, joined with `{16}`, `{24}`, … across the
loop back edge. Cells join through `MemEnv.widen_join`
(cbat_ai_representation.ml:242/289) → `Val.widen_join`
(cbat_ai_memmap.ml:314) → `WordSet.widen_join`
(cbat_clp_set_composite.ml:244) → `Clp.widen_join` (cbat_clp.ml:1074):

```ocaml
else if subset p1 p2 then
  if equal p1 p2 then p1 else
  let step = step_of p2 in
  if W.is_zero step then top (bitwidth p2)
  else infinite ((base_of p2), step)
```

`Clp.infinite` (cbat_clp.ml:99) then factors the step and REDUCES THE
BASE MODULO IT: `base = W.modulo b step` — `8 mod 8 = 0`. The widened cell
value becomes `{base=0, step=8, cardn=2^61, is_inf}` = every 8-aligned
address in the 64-bit space, printed as `{0..0xFFFFFFFFFFFFFFF8}^inf`.
**The lower bound "+8 or above" is erased by the mod normalization** —
and this is load-bearing for the domain, not a bug in isolation:
`finite_end` (cbat_clp.ml:136) computes `base + step·(cardn−1)` in
wrapping arithmetic and `subset` (cbat_clp.ml:291) runs the `Some e1,
Some e2` arm's `in_bounds` test against those wrapping ends; an infinite
set's canonical form is its circular RESIDUE CLASS (all words ≡ base mod
step), and the mod normalization of the base is what makes that
representation closed under the domain's operations (a hypothetical
"base 8, unbounded above" form would wrap its end to a small number and
spuriously subset finite sets). The words lane has landmarks (Simon &
King port) but **memory cells carry none** (documented scope, AGENTS.md),
and even for words, a landmark needs an observable guard boundary; the
overflow pointer is never compared against anything, so no landmark can
be acquired for it. And note the TRUE abstract fixpoint value IS the
unbounded ascending set {8,16,24,…}: `count` arrives in a register (TOP
intra-procedurally), the loop is unbounded from the callee's view, so NO
widening cleverness can make it finite. The loss that matters is not
"infinite" — it is that "ascending from +8" became "all 8-aligned
words".

**Step 3 — Channel 2 refuses the infinite set.** `is_seed`
(cbat_vsa.ml:2896) channel 2 requires the denoted address to be a
**bounded, finite SUBSET of the frame neighborhood** (±64K, spec §2.2
generous-constants rule):

```ocaml
else if WordSet.is_infinite ws then false
```

An infinite set is never a subset of the bounded neighborhood → the deref
is not a seed → untagged. This refusal is a *sound* non-seed (the raw-
memory fallback), per ADR-0003's "SUBSET, never INTERSECTION" doctrine —
but it throws away a value that is still *structured*: every element of
{0,8,16,…} is a non-negative anchor-relative offset with stride 8.

**The last-mile wrinkle — `is_positive_kind` is strict.** Even if the
deref were tagged with today's infinite set, `classify` would produce
`Infinite(0, hi)` and `is_positive_kind` (convutils.ml:149) requires
`kind_lo > 0` — `lo = 0` fails. The 0-element must not be admitted: it
denotes the callee's own entry SP (the retaddr slot), not the caller's
arg area; a grant keyed on lo=0 would rebase an access that may touch the
retaddr cell onto `hike_stack + 0` — wrong by exactly the retaddr slot.
`hike_stack`'s coordinate base is the caller's entry RSP (one 8-byte slot
above the callee's `+0`), and the incoming-arg cells sit at `+8` and
above (probe: `sum12`'s args are read at `hike_stack+8…+48`, i.e. tags
`Range(16,16)…` in callee-entry-SP coordinates — a consistent
two-slot-shi; the strict `> 0` is what keeps the bases honest).

The second untagged deref in `two_pass` (`%00000bbb`, RAX=TOP) is the
same class one level deeper: ap2's overflow cell is written by the
va_copy store `mem[RCX+8] <- RDX` (pointer-indirect destination) and read
back after an intervening `printf` call; at the fixpoint the load-back
denotes TOP (the cell state at that block is top — either the copy store
resolves to a different cell than the read expects, or the
frame-keeping call abstraction's `keep_lo` boundary (call-time RSP)
clobbers the below-RSP cells; the exact arm is not pinned and is left as
the first verification item for the implementation lane). TOP is again a
sound non-seed.

**T02 candidate re-verdict (audit02.exe, today):** candidate 1
(rewrite_addr unchanged) — DEAD for these defs (rewrite works for the
cells; it fails only for RAX, which is the symptom not the cause);
candidate 2 (denote returns TOP) — DEAD (denote returns the infinite set,
not TOP — for `sum_n`; TRUE for vacopy's second deref as above);
candidate 3 (Error/val_as_imm) — DEAD; candidate 4 (partitioned vs
sequential divergence) — DEAD (probe runs the same sequential walk and
reproduces; the loss is in the fixpoint's cell value, not the tag-state
merge). The T02 audit pre-dates the restriction removal; its "Unbounded"
presentation is obsolete — the current presentation is UNTAGGED (no
`vsa_info` entry at all, not `Unbounded`).

## 3. What the upstream CBAT VSA does for this shape

Provenance: `src/cbat_vsa/` was vendored in commit `4c84296`
("recover-golden", 2026-08-28, ~21K insertions: "vendored CBAT
value-set-analysis library (AI, Mem, WordSet, Clp, contextual fixpoint,
the Bourdoncle-WTO driver…)"), copyright header "Draper Laboratory…
ONR/NAWC Contract N6833518C0107" — CBAT is Draper's CBAT/Beagle-line
toolkit. In the vendored code there is no region mechanism: `AI.t` is
`{ memories : MemEnv; words : WordEnv; frame : frame option }`
(cbat_ai_representation.ml:242ff) — values are anchored integers, cells
key by SP-relative offsets, and an address set is a raw CLP with no
provenance. The upstream papers' region-based value-set (below) was NOT
carried over; hike's Channel 2 (ADR-0003) is the port's own substitute
for it, and its bounded-subset admission rule is where the port stops
short of the upstream idea's reach. (Upstream repo not vendored; claim
scoped to the vendored tree.)

## 4. What classic region-based VSA does differently

- Gogul Balakrishnan & Thomas Reps, "Analyzing Memory Accesses in x86
  Executables" (CC 2004), §4: every abstract value is a finite set of
  (region, offset-interval) pairs; regions are named address-spaces
  (stack regions per call-chain position, heap, globals). A pointer
  stored into a stack cell and reloaded still carries the STACK REGION in
  its value-set, so `mem[RAX]` resolves as a stack access **independently
  of the offset's boundedness** — the region is the residency proof; the
  interval only refines. Walked pointers stay in-region: the join
  {(stk,+8)} ⊔ {(stk,+16)} = {(stk, [8,16])} ⊔ … widens the interval to
  [8,+∞) with the region intact.
- Balakrishnan, Reps, Melski, Teitelbaum, "WYSINWYX: What You See Is Not
  What You eXecute" (TOPLAS 2010), §5 (a-locs & value-sets): per-region
  abstractions let memory-carried pointers remain first-class; a memory
  access is summarized per-region rather than per-address.

In hike's anchored model the "region" role is played by the ANCHOR
coordinate system (every value is anchor-relative), but the CLP does not
remember WHICH coordinate system its numbers came from — a heap pointer
and a walked stack pointer are the same shape of number. The two designs
below transplant the missing "region stays attached through memory and
widening" property in minimal forms.

## 5. Ranked improvement designs

### Design 1 — a stack-provenance lattice bit on cell values ("channel 3")

**Mechanism.** `Val.t` (the per-cell value, cbat_ai_memmap.ml:~300) gains
a `provenance : prov` field, `prov = Stack | Unknown` (a two-element
lattice, Stack ⊑ Unknown). Producers: (a) when `denote_exp` stores a
value whose expression's SP-derivedness is PROVEN — i.e. `rewrite_addr`
succeeds on the stored value's expression (the frame relation says it is
affine over SP/FP: `RBP + 0x10` → yes; a loaded heap value → no) — the
cell's prov bit is set to Stack; (b) loads propagate the cell's prov into
the loaded word's prov (needs a parallel bit on `WordEnv` values or a
side set keyed by var). Joins widen conservatively: Stack ⊔ Stack =
Stack, anything-with-Unknown = Unknown. The deref consults it: a Load
whose address's prov = Stack is a stack access (seed), regardless of the
offset CLP's infiniteness; the offset tag is then whatever `classify`
gives (`Infinite(0, hi)` today).

**Plug-in points.** `Val.t` + `Val.join/widen_join` (cbat_ai_memmap.ml),
`WordSet`/`WordEnv` prov side-lane or a `var → prov` map in `AI.t`
(cbat_ai_representation.ml), store in `denote_exp`'s `Bil.Store` arm
(cbat_vsa.ml:~401), load in the `Bil.Load` arm (cbat_vsa.ml:~383), seed
decision `is_seed` (cbat_vsa.ml:2896), classification `extract`
(cbat_vsa.ml:2929), consumer `compute_sub_sig`/`is_positive_kind` chain.

**Soundness.** The prov bit is computed by a monotone function of the
same fixpoint state (store-of-proven-SP-affine ⇒ Stack; join is
conservative): if a reachable execution stores a heap address into the
cell, the value's expression is NOT SP-affine at that point, so prov =
Unknown there, and the join with the SP-affine path is Unknown — the
deref never sees Stack prov unless EVERY joined value is proven
SP-derived. The bit can only over-approximate "may be SP-derived", never
fabricate it. Idempotent with the CLP: the bit adds no numeric
constraint.

**Why it wins where widening can't.** The walked pointer's TRUE abstract
value IS infinite; no widening improvement recovers boundedness. The prov
bit carries the ONE fact that survives: every reachable element is
anchor-relative.

**Residual gap for THIS bug.** Provenance alone yields tag
`Infinite(0, hi)` (the mod-normalized CLP) — `is_positive_kind` still
fails on `lo = 0`, and the emission's positive-rebase lane
(`rebase_addr`, bil2llvm.ml:886) is keyed on positive tags. Closing the
bug end-to-end therefore ALSO needs the offset admission fix of Design 2
(the lo-strictness / two-slot base). The prov bit is the *residency*
half; Design 2 is the *positivity* half.

**Blast radius.** Cells/words gain a field: every `Val`/`WordEnv`
construction site (moderate churn; mechanical). The 33 passing binaries:
prov = Stack on cells whose stored values are SP-affine — the deref seed
set GROWS (more defs seeded than today's channel-2 bounded-subset). New
seeds become stack accesses that today take the raw-memory fallback —
each must still emit correctly (the frame/hike_stack lanes exist) — and
the write-closed region rule in stack_to_locals already handles
`Infinite` tags conservatively (region stays memory). Risk: moderate —
the tag-set changes corpus-wide (the C8 baseline's "identical tag kinds"
bar would move by design; needs a fresh A/B with the tag-count census).

**Cost.** Medium (domain plumbing, ~6 sites, no fixpoint-structure
change).

### Design 2 — directional infinite admission: bounded-below strided sets (paired with 1)

**Mechanism.** Keep the CLP as-is (mod-canonical, circular — leave the
domain alone) and let the SEED/TAG pipeline admit infinite sets when the
*seed-side* can prove the ascending direction. Two sub-parts:

(a) **Seed admission.** Channel 2 gains a case: an infinite set is
admissible as a stack seed iff its signed lower bound ≥ 0 (or > 0 for
granting) — using the MIN ELEM of the set, which for the mod-normalized
{0,8,…} is 0 — AND the set admits no negative multiples: today's set
{0,8,…,0xFFFFFFF8} as a SIGNED set spans both sides (0xFFFFFFF8 = −8), so
plain min-elem admission is WRONG for the mod-normalized form. The sound
admission must therefore reject the mod-normalized infinite set — which
collapses (a) into: no new admission without a directional
representation. So (a) cannot stand alone; it is exactly the reason
Design 1's prov bit (or 3's directional CLP) is needed: SOMETHING must
attest the direction.

(b) **The `is_positive_kind` base.** With a directional attestation
available (from 1 or 3), the deref's tag should be built from the *chain
lower bound*, not the mod-normalized base: the prov-producing store saw
`+8`; the walk preserves ≥8. The tag `Infinite(8, +∞)` then passes
`is_positive_kind` (8 > 0) and the `hike_stack` grant, and the emission
rebases onto `hike_stack + offset` — reproducing the original pointer's
numeric value at runtime (the abstract attestation says every reachable
value is anchor-relative; the rebase emits `hike_stack + (value −
anchor)`, identical to `value` — sound by construction).

**Soundness.** The directional attestation must be a fact about ALL
reachable values of the deref's address (monotone join), never an
intersection/meet with a neighborhood (ADR-0003's doctrine — never
intersect to fabricate residency). Design 1's prov bit + a "min-elem ≥ 8"
that comes from the SAME lattice (see 3 for the alternative) satisfies
this.

**Blast radius.** `is_seed` + `classify`-to-tag + `is_positive_kind`
consumer (3 small sites) + the emission rebase lane (exists). The other
33 binaries: only affects defs that today are untagged AND
provenance-Stack — strictly more seeding, same emission machinery as
`many_args`' working positive-infinite lane.

**Cost.** Small once (1) or (3) provides the attestation.

### Design 3 — directional infinite CLPs (the domain change)

**Mechanism.** Extend `Clp.t`'s infinite sets with a direction
(`Ascending | Circular`): `infinite()`'s mod-normalization applies only
to `Circular`; an ascending widening keeps `base = min(base1, base2)` and
the chain's stride. `subset`/`finite_end` respect the direction (an
ascending infinite set has no wrap end; note `finite_end` at
cbat_clp.ml:136 returns `None` only for bottom — the `| None, _ -> true`
arm of `subset` (cbat_clp.ml:291) is the bottom-⊆-anything case, and
infinite sets currently flow through the wrapping `Some/Some` arm —
an ascending form needs its own arm there; today's circular handling
should be audited in the lane: whether `in_bounds` on wraparound ends
ever admits an infinite set into a finite one's subset relation).

**Soundness.** Ascending widening is the classic interval-widening-with-
stable-bound (keep the non-moving bound, extrapolate the moving one);
the self-correction path is the plain-join fallback when a later iterate
escapes the kept bound (subset fails → join → wider) — the standard
argument. The representation is strictly more informative than today's
circular form (ascending ⊆ its circular collapse), so no consumer gets
less precise.

**Blast radius.** THE domain: `create/infinite/widen_join/subset/
equal/compare/min_elem/max_elem/translate` + every consumer of infinite
sets (mem-fission's `Infinite`-span regions, `classify`'s `Infinite`
tags, `k_range_of`, the backward lane's cell meets
`constrain_cell_on_trace`). High blast radius: any change to infinite-set
equality risks the fixpoint's termination (the widening points compare
states for stability — cbat_wto/cbat_vsa's per-head checks). The lane
would need the full `clpequiv` differential sweep (the word-substrate
lane's reference-vs-new harness, `zz_scratch_probe/clpequiv.ml`) plus
tag-census A/B over the corpus plus IR byte-identity on the 33.

**Cost.** High; the deep-but-risky option. It subsumes 2 (the
directional attestation becomes the CLP's own `min_elem`) and makes 1
unnecessary for the seed (still useful for heap-vs-stack
disambiguation). Note `Clp` is shared by the whole corpus — this is a
re-baselining session by nature (region ids and tags would shift), like
the word-substrate lane.

### Design 4 — per-def lookback: seed the deref from the pointer's producing chain (rejected)

Seed `mem[RAX]` by walking RAX's def-use chain to the `RAX := RBP+0x10`
producer through the cell (a syntactic backward slice), tagging the deref
with the producer's offset. Rejected: a syntactic chain is not a sound
proof of the LOAD-BACK's value (the cell may have been overwritten by a
non-affine store on another path; the chain is path-insensitive), and it
re-implements (badly) what the fixpoint's cell map already computes —
the same "two mechanisms that can disagree are worse than one" argument
that killed the T04 inline-relevance option (ADR-0003). Also violates the
no-AST-pattern-matching principle for memory operands in spirit (it
matches a specific producer shape). Recorded for the record.

### Design 5 — pure consumer-side fix: grant `hike_stack` on a weaker signal (rejected)

Grant `hike_stack` whenever the sub has ANY tagged stack access (or
always), decoupling the grant from positivity. Rejected: the grant's
cost-free part isn't the problem — the DEREF's emission must be anchored
on the caller's arg area (`hike_stack + positive`), and emitting that
without a residency/positivity proof fabricates addresses (the rebase
lane itself asserts "positive interval but no stack param" —
bil2llvm.ml:891 — the emitter is built around the proof being real).
This is the unsound direction (the array_local-class lesson: soundness
over precision, always).

## 6. Recommended path and validation plan

**Recommendation: Design 1 + Design 2 (provenance bit + directional
admission at the seed/tag/consumer seam), leaving the CLP domain (3)
alone.** Rationale: the prov bit is exactly the region-based-VSA idea
transplanted at minimal depth into the anchored model (the anchor already
plays the region role; the bit plays "is in-region"); the admission+tag
fix is three small sites; the CLP change (3) is a full re-baselining
session for a fact that can be carried without touching the domain. The
pair is sound by the monotone-provenance argument and uses only existing
emission lanes (`many_args` proves the positive-infinite lane end-to-end:
`hike_stack + 8; inttoptr; load` is byte-correct there TODAY).

**Open item for the lane's first session (from §2):** pin the exact arm
of vacopy's `%00000bbb` TOP (copy-store cell resolution vs the
frame-keeping `keep_lo` boundary after `printf`); the probe (`vsa_ptr_diag`)
already prints the needed state lanes for it.

**Validation plan (the repo's bar):**
1. `dune runtest` green (467-check suite; add fixtures: a synthetic
   store-pointer→loop-walk→deref sub asserting the tag is
   `Infinite(lo>0, hi)` and the grant fires; a negative fixture: a heap
   pointer stored/loaded must NOT seed — prov stays Unknown).
2. Corpus emission 35/35 rc=0; `vsa_ptr_diag` on `sum_n`/`two_pass` shows
   the two derefs seeded with positive-lower-bound tags.
3. Semantic gates: `variadic` and `va_arg_vacopy` FLIP to PASS (the two
   knowns T02/T03-class close or move materially); the other 33
   byte-identical (IR byte-identity — the strictest available control;
   note the prov bit may legitimately add tags on OTHER binaries — any
   IR diff outside the two must be shown strictly-better: seeded accesses
   that previously took the raw-memory fallback now taking the
   frame/hike_stack lanes).
4. `check_allocas.sh` (no new sp-derived GEP violations; count moves only
   in the strictly-better direction), semantic-opt gate (opt-safety), the
   8-bin oracle 8/8.
5. Tag-census A/B (the C8 worklist lane's methodology: tag kinds per
   heavy sub, byte-equal multisets expected on untouched subs).
6. Performance: stage_timer on `sort`/`grep`/`gcc-12` heavy subs — the
   prov join must be cheap (one lattice bit per cell/value join; expected
   noise-level).

## 7. Sources

- `src/cbat_vsa/cbat_vsa.ml:284` (`rewrite_addr`), `:375` (`denote_def`
  frame rewrite), `:383/:401` (Load/Store denote arms),
  `:2896` (`is_seed` channel 2 — the bounded-subset rule),
  `:2929` (`extract`'s classification walk), `:2828-2831`
  (`classify`, Infinite).
- `src/cbat_vsa/cbat_clp.ml:36` (`t` record), `:99` (`infinite` — the
  `base mod step` normalization), `:1074` (`widen_join`), `:136`
  (`finite_end` — wrapping end computation), `:291` (`subset` — the
  `Some/Some` wrapping `in_bounds` arm), `:229` (`equal` — structural).
- `src/cbat_vsa/cbat_clp_set_composite.ml:244` (`widen_join` lift).
- `src/cbat_vsa/cbat_ai_representation.ml:242/289` (state join/widen),
  `:242` (`AI.t` fields — no provenance lane today).
- `src/cbat_vsa/cbat_ai_memmap.ml:314` (`Val.widen_join`), `:482`
  (`call_keep` — the frame-keeping escape rule).
- `src/hike.ml:154-168` (`compute_sub_sig` — the `has_positive` grant),
  `:305-316` (the `_start` filter, unrelated but the same two failing
  binaries' other half).
- `src/convutils.ml:149` (`is_positive_kind` — strict `> 0`).
- `src/bil2llvm.ml:886-891` (`rebase_addr` — the positive-rebase lane),
  `:1093-1109` (`create_call_args`' `hike_stack` threading), `:1814`
  (hike_stack = caller entry RSP).
- `docs/adr/0003-remove-restriction-vsa-seeding.md` (channel 2's design
  intent and the SUBSET-not-INTERSECTION doctrine; the T04 rejection).
- `.scratch/restriction-removal/spec.md` §2.2 (the frame-neighborhood
  constant, ±65536).
- `.scratch/one-frame-anchor-removal/issues/02-vsa-value-tracking.md`
  (T02 — the pre-restriction-removal audit; candidates re-verdicted in
  §2 above).
- Probe evidence: `zz_scratch_probe/vsa_ptr_diag.ml` (scratch),
  outputs quoted in §1-2; `bap --dump=bil` of both binaries
  (/tmp/opencode/{variadic,vacopy}_bil.txt).
- Gogul Balakrishnan & Thomas Reps, "Analyzing Memory Accesses in x86
  Executables", CC 2004, §4 (region-based value-sets).
- Balakrishnan, Reps, Melski, Teitelbaum, "WYSINWYX: What You See Is Not
  What You eXecute", TOPLAS 2010, §5 (a-locs, per-region value-sets).
- Vendoring provenance: commit `4c84296` (recover-golden) — Draper
  Laboratory CBAT lineage (file header, ONR/NAWC N6833518C0107).
