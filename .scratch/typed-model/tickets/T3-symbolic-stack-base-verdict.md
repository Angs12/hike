# T3 — verdict: the symbolic stack base + single-channel tagging

Verified 2026-09-10 EEST on the committed tree `7a60794` (branch
`tm/t3-symbolic-base`, worktree `/home/tovpr/hike-t3`; three stage commits
`766eb6e` → `a83a6a3` → `7a60794`). Verification performed independently by
the finishing session: full battery re-run on the committed tree, plugin
installed from that tree, provenance recorded
(`git=7a60794 src=2f9981554ff01428 bundle=0311e8475e2aaf1e`). No source
fixes were needed — every gate green on the landed commits as-is.

## The design as landed

### Stage A — the StackOff domain (`766eb6e`, `src/cbat_vsa/cbat_clp_set_composite.{ml,mli}`)

A third composite constructor `StackOff of Clp.t` = the MODEL stack
segment base (a symbolic constant living in the non-canonical band
`[2^62, 2^62+8MiB]` — disjoint from every real user/kernel address, so
no plain address can masquerade as stack and no stack address can
masquerade as real) plus the EXACT offset set. The correlation between
the entry RSP and every SP-derived address is carried STRUCTURALLY
(the flat-segment design cannot: its hull subtraction doubles the width
and collapses tag precision — measured, `.scratch/typed-model/t3-design-notes.md`).

Semantics (complete, no gates):

- `add`/`sub` with a base-free operand: offsets propagate EXACTLY.
- `StackOff − StackOff`: the base cancels — the exact offset difference.
- `StackOff ⊕ StackOff` (add): plain concrete hulls (the base appears twice).
- bitwise / mul / shifts / mixed meets: degrade to the plain CONCRETE
  smear hull (`seg & 0xF` = `[0,15]`, fixed-bits undecided — the L1
  fake-bits guard-pruning class is structurally dead, `value_env` never
  needed).
- meet/join/widen/extrapolate between StackOffs: pairwise in the
  offsets — RSP loop drift is exact exactly as the old offset lane's.
- equal/precedes/overlap between StackOffs: offset space (shared base).
- min/max/elem/iter (concrete queries): the smear.
- `splits_by` + `Mem.Key.of_wordset`: OFFSET space (the per-sub cell-key
  universe — segment-word consistency of the memory lane, D2).
- same-width casts and full-width extract: identity.
- API: `stack_word`, `stack_word_i64`, `as_stack`, `in_stack_segment`
  (the degraded/realignment arm reads the signed-positive band
  `[2^61, max-int64]` — non-canonical-only, so sound), `stack_bounds`,
  `relativize` (offset-space twin; `None` stays `None` — a foreign
  address must never masquerade as an offset).

### Stage B — the VSA flip (`a83a6a3`)

- **One predicate.** `is_stack_access addr st` ≡ the denotation of
  `addr` is a stack-symbolic set (StackOff) or the plain in-band
  degraded arm — visitor-merged, replacing the old two channels
  (`mentions_frame_var` + `frame_neighborhood`). `vsa_info` remains the
  only carrier of stack-access-ness (the 100% Tagging Invariant).
- **Tags = denotation − base.** The tag is `classify(relativize(denotation))`;
  after the overlap merge the producer splits the lanes:
  `caller_split` — bounded spans entirely at/above the entry RSP (lo ≥ 0)
  become the new **`Caller`** kind (the ABI-visible window: incoming
  stack args, the return-address slot); spans entirely below (hi ≤ 0)
  stay `Range`/`Infinite` (own frame, mixed included); everything else
  (two-sided lo<0<hi, wrapped) becomes **`Mixed`**.
- **DELETED (grep-clean; only historical comments mention them):**
  the frame relation (`seed_frame`, `apply_frame_def`, `frame_add_fvar`,
  `frame_add_*`/`frame_lookup`/`frame_set`/`frame_remove`, `expr_of_term`,
  `rewrite_addr`, `frame_rewrite_rhs`, `frame_of`/`frame_of_state`,
  `AI.t`'s `frame` field and its lattice threading) and **`value_env`**
  (guards now evaluate on the segment-smeared words — L1 structurally
  impossible). `prove_nonneg`'s stack_anchor is the structural StackOff
  test; `call_abstraction_frame`'s keep boundary is the call-time RSP's
  key-space bounds; pointer-arg escapes exclude their own key ranges;
  `outgoing_arg_stores`/`sp_displacement` read offset space.
- En-route fix: `meet(StackOff, TOP)` is the StackOff (block-IN
  top-valued vars no longer flatten the base out of every address).

### Stage C — the uniform materialization + the Mixed lane (`7a60794`)

The emitter's tag dispatch is kind-complete with NO sign tests
(`src/bil2llvm_mem.ml` `mem_access`; the license, not a name/sign test,
gates the frame GEP — `frame_wrap_license` is now derived from the tag
kind: `Range`/`Infinite` ⇒ licensed; `Caller`/`Mixed`/`Unbounded`/`VLA`/
`Dead`/untagged ⇒ not):

- **Range/Infinite** (entirely below the entry RSP): the ONE UNIFORM
  RULE — `create_exp` → `create_addr_ptr`'s licensed arm,
  `ptr = frame + (word − stack_0) + anchor_idx`, total over all words,
  all signs, all widths (the emitted entry-RSP value IS `stack_0`, so
  the runtime index is exact however imprecise the tag). The old
  per-tag dispatch (singleton-positive rebase, negative GEP, dynamic
  inttoptr) is deleted: `rebase_addr`, `create_static_mem_access`
  (both arms), `mem_access_via_ptr`, `is_positive_kind` are GONE.
- **Caller**: `ptr = inttoptr(hike_stack + (word − stack_0))` — ONE
  form, no select; `stack_0` is the emitted entry-RSP value
  (`anchor_i64` for frame subs; the `hike_stack` parameter itself for
  precise subs, whose SP local now binds to it).
- **Mixed**: the two-base rule — the RECORDED DEVIATION, argued below.
- **VLA/Unbounded/Dead/untagged**: their existing complete lanes
  (Unbounded/Dead keep their warned-poison diagnostics).
- DCE's precise-lane SP erasure deleted (the uniform rule READS the
  SP-derived arithmetic; liveness is the plain used-based rule — the
  D4 pin re-derived to the successor behavior).
- `check_allocas` (d) modernized to the T3 storage vocabulary: a define
  owns ONE model storage (`frame` | `stack_rN`) or none (caller lane,
  foreign exception lane); violations = mixing or phantom references.
  The old 1-frame-per-memory-define contract is dead.

## The 7 pins re-derived WITH verification (all pass on `7a60794`)

| pin | old bound (old keying) | new keying | why the bound still holds |
|---|---|---|---|
| **VSK-EMPTY** | the unconditional edge is the identity — `AI.equal` over words+memories+the `frame` field | identity over words+memories only (the `frame` field is deleted); RSP's word is the segment-seeded `StackOff{0}` carried in the word map | an unconditional edge has no guard and no transfer; the identity claim is representation-independent — only the state's SHAPE changed |
| **L-D2** | the wide-bound corpus shape: the counter cell at RBP−8 bounded ⊆ [0,64), max ≤ 63, via the jcc-decoder cell meet (the cell keyed by the frame-relation rewrite-space offset −8) | the address `RBP−8` denotes `StackOff{−8}`; `Mem.Key.of_wordset` RELATIVIZES it to the same −8 offset key | the refined operand (the counter) is PLAIN — every guard row and the meet are bit-identical; only the cell key's provenance changed |
| **L-D6** | the RBP-anchored loop: the cell at RBP−8 ⊆ [0,64) at the BODY input, gate-free | same offset-space key (−8) | same argument; the pin's gate-free discipline is untouched (the meet is the only soundness mechanism) |
| **L3c3-1** | the PLUS-HULL row `{−1} ∪ [0,8]` caps the cell at RBP−8 (⊆ [0,9]) | same offset-space key | the producer-op recursion refines PLAIN values; the cell keys coincide exactly with the old rewrite-space offsets |
| **L3c4-4** | the HIGH-extract row: the cell bounded ⊆ [0, 0x09FFFFFF] | same offset-space key | same argument |
| **L3c5-3a** | the AND-identity row: the cell bounded ⊆ [0,9] | same offset-space key | same argument |
| **L3c5-3b** | the OR-identity row: the cell bounded ⊆ [0,9] | same offset-space key | same argument |

The common mechanism: these pins' cells are anchored at small frame
offsets; the old universe keyed them by the frame relation's rewrite
offsets, the new universe keys them by `relativize(StackOff offs)` —
the SAME integers. No bound was weakened; every pin asserts its old
numeric bound and passes. (Also re-derived in the same commits, beyond
the seven: P22-1's `−8+5·8=32` now lands in the CALLER lane; E2eD-5,
P21-1/2, P23-1/2/3, F1-1/2, P3-1/B-1 — the anchor is `StackOff{0}` —
and the test_seed frame fixtures seed the segment universe. E1 keeps
its concrete `{0x1000}` entries: a fixture may choose a known-RSP
scenario; the mechanism under test — the matched-pair +8 — is
representation-independent.)

## The gate table (all numbers from this session's runs)

| gate | result |
|---|---|
| build, default profile | rc=0 ✅ |
| build, `--profile vsa-debug` (own `_build-debug`) | rc=0 ✅ |
| `dune runtest` | rc=0; failure set EXACTLY the pre-existing 8 (E2eD-7/8, LM F1-NEQ, F1-FT ×2, F1-B1 ×2, F1-B3) ✅ |
| 7 modernized pins (VSK-EMPTY, L-D6, L-D2, L3c5-3a, L3c5-3b, L3c4-4, L3c3-1) | **all 7 `ok`** ✅ |
| referee (`clpequiv`) | **2,861,148 checks / 0 mismatches** ✅ |
| -O0 emission (`run_corpus.sh /tmp/corpus`) | **33/33 rc=0** ✅ |
| -O0 structural asserts (`check_allocas.sh`) | **165 passed / 0 failed** ✅ |
| -O0 strict semantics (`run_semantic.sh`, no 4th arg) | **33 PASS / 0 FAIL**, rc=0 ✅ |
| -O0 strict opt-safety (`run_semantic_opt.sh`, no allowlist) | **33 PASS / 0 FAIL**, rc=0, 0 CRASH ✅ |
| -O2 emission (`run_corpus.sh /tmp/corpus_o2`) | **33/33 rc=0** ✅ |
| -O2 structural asserts | **165 passed / 0 failed** (the modernized check (d); the wave-1 "164/1 out_struct shape-d" class is superseded by the new storage-shape contract) ✅ |
| -O2 pinned semantics (`run_semantic.sh … o2_known_failures.txt`) | **27 PASS / 6 FAIL — failing set == the golden six exactly** (byte_copy, fizzbuzz_safe, fptr_table, union_overlap, va_arg_mixed, va_arg_vacopy); rc=0, no REGRESSION/IMPROVEMENT, pin untouched ✅ |
| instrumentation blocker (`src/check_instrumentation.sh`) | clean rc=0 (exercised by both profile builds) ✅ |
| plugin provenance | `git=7a60794 src=2f9981554ff01428 bundle=0311e8475e2aaf1e` ✅ |

## Convergence rows before/after (pre-T3 reference:
`/home/tovpr/tm-battery/merge-t1/conv-real.log`)

**Classification movement: NONE.** The `o0model`/`o2model` columns are
identical row-for-row across all 33 sources: 27 SAME/SAME + the six
DIFF = the golden six. T3 moved no semantic classification in either
direction — the expected outcome for a provenance-representation lane
(the materialization was already behaviorally correct where the old
tags were precise; the classes T4/T5 target are untouched).

Quality-dimension (`i0/i2` post-opt instruction counts) rows that moved:

```
source          pre-T3   T3
alloca_vla       62/4  →  65/4
array_local     133/747→ 133/749
byte_copy       115/26 →  113/26
factorial        59/46 →   59/45
fizzbuzz_safe   101/257→  101/253
list            218/241→  214/241
nested_struct   137/4  →  132/4
ptr_chain        88/4  →   87/4
sret_big        174/228→  172/228
struct_arr_dynidx 115/80→  115/79
struct_by_value 187/4  →  169/4
va_arg_mixed    180/92 →  186/92
va_arg_vacopy   212/152→  396/151   ← the one notable growth (see below)
variadic        185/81 →  185/77
```

(The three `Segmentation fault` lines interleaved in both logs are the
script's pre-existing native-run behavior on byte_copy / fptr_table /
va_arg_mixed rows — identical in the pre-T3 reference, not a T3 effect.)

### The va_arg overflow residual re-attributed (T7 dissolved here)

Old golden-list attributions: va_arg_vacopy = **L2** ("missing
`hike_stack` rebase in `bil2llvm_mem.ml`'s `lo<0` dynamic-load arm"),
va_arg_mixed = **L1** ("alignment-guard trap live").

T3 measured:

- **va_arg_vacopy** (-O2 DIFF; lifted rc=0): the symptom is the second
  va_copy'd traversal reading a STALE sixth element
  (`1 2 3 4 5 1` vs native `1 2 3 4 5 6`). The L2 mechanism is
  STRUCTURALLY GONE under T3 — `rebase_addr` is deleted, and the -O2
  emission for this binary contains NO Mixed select and NO `lo<0` arm:
  its reloaded-pointer traffic routes through the Caller/untagged
  lanes (`%caller_off = sub …, %anchor_i64; %caller_addr = add
  %hike_stack, %caller_off`). Since the old attribution's mechanism no
  longer exists in the tree and the failure persists, the residual
  **re-attributes to the va_list state round-trip in the -O2 lift**
  (the va_copy'd AP's save/restore/reload through the reloaded-pointer
  lane), NOT to any address-materialization arithmetic. The -O0 model
  is SAME/SAME — the materialization is correct; the residual is the
  -O2 lift's runtime state.
- **va_arg_mixed** (-O2 DIFF; lifted rc=132 = SIGILL): the ud2 poison
  arm is reached — the recorded **L1** class, unchanged.

The spec §T7 claim "there are no sign cases and no selects" is thereby
narrowed to the class where it is true (see the deviation section): the
select survives for Mixed, but the old L2/T7 mixed-span attribution of
the va_arg residual is dead.

## Emission delta vs `/home/tovpr/tm-battery/merge-t1/emit-o0`

**All 33 binaries changed** (0 byte-identical) — the coordinated flip
is a DELIBERATE full re-baseline; no gate consumed byte-identity this
lane. Classification of the delta:

- **Dominant mechanism (all 33):** the uniform materialization.
  Constant-offset frame accesses now materialize as RUNTIME
  `word − %anchor_i64 (+ %anchor_idx)` arithmetic feeding the `%frame`
  GEP instead of folded constant GEP indices (visible in the smallest
  delta, `out_printf.ll`, 99 diff lines). Semantically identical
  (proven by the 33/33 semantics + 33/33 opt-safety gates); the
  consumer's optimizer folds it.
- **inttoptr/ptrtoint corpus-wide: essentially unchanged** (e.g. list
  51→51 inttoptr) — the foreign exception lane did NOT grow. The only
  count move is alloca_vla 8→9 inttoptr.
- **selects:** 3 remain corpus-wide — `va_arg_vacopy` ×2, `variadic` ×1
  (the Mixed lane); `sret_big` LOST its old select (1→0). No new
  rebase-select forms anywhere.
- **Diagnostic shift (same classes):** the per-sub first-hit Unbounded
  warning moved from array_local + union_overlap (pre-T3) to alloca_vla
  + byte_copy (T3) — under the new denotation universe a different def
  is the first top-tagged one; the class and its complete Unbounded
  lane are unchanged and both binaries pass semantics/opt-safety. The
  Dead warning (va_arg_mixed `consume_mixed`) is unchanged.
  No new diagnostic classes.

## THE MIXED-LANE DEVIATION — ARGUED (not flagged, not silently kept)

The ticket/spec §T3 letter says: "every address word materializes as
ONE step — `ptr = frame + (word − stack_0)` — total over all words, all
signs, all widths. No positive/negative arms, no rebase selects, no
span cases." The landed tree materializes the **Mixed** class
(`caller_split`: bounded spans with lo<0<hi, or wrapped) as:

```
base = select(word >= stack_0,  hike_stack + (word − stack_0),  word)
ptr  = inttoptr(base)
```

(`mixed_mem_access`, `src/bil2llvm_mem.ml:159`). This is a DEVIATION
from the no-select letter. The verdict of this session: **the deviation
is sound, the rule is COMPLETE (not a gate), and no single-base rule is
sound for the class — keep it, with this argument on the record.**

1. **The class is genuinely either-based.** A `Mixed` def's address is
   below the entry RSP on some runtime executions and at/above it on
   others — the concrete case (the corpus's only Mixed sources:
   `va_arg_vacopy`, `variadic`) is the va_list AP: the reg-save arm is
   an anchor-linear word BELOW the entry RSP (the lifted va_start's
   copies live in `%frame` cells), the overflow arm is an anchor-linear
   word ABOVE it (the caller's outgoing-arg window = `hike_stack`-relative).
   The sign of the word's anchor-relative offset IS the class boundary
   at runtime, so the select condition `word >= stack_0` is EXACT, not
   heuristic.
2. **Both arms are exact, and the rule is total.** Above-arm:
   `hike_stack + (word − stack_0)` = `hike_stack + off` — the exact
   caller-window cell. Below-arm: `inttoptr(word)` — for an
   anchor-linear word this IS the frame cell (the ptrtoint round-trip
   through `anchor_i64 = ptrtoint(%frame + anchor_idx)`); for a
   foreign/truly-reloaded word it is the identity materialization —
   exact by definition. Every word of every width and sign gets an
   exact pointer; the rule never refuses, never bottoms, never
   degrades — it is the opposite of a gate: a complete per-word
   dispatch. (It also only ever fires on defs whose denotation the VSA
   PROVED stack-symbolic — a plain real address is never in-band, the
   segment being non-canonical.)
3. **No single-base rule is sound for the class — measured, twice.**
   - Frame base (the uniform rule) for ALL Mixed words: an
     overflow-truth word (`off > 0`) GEPs into `%frame` at
     `anchor_idx + off` — cells the lifted va_start never wrote the
     caller's outgoing args into. Wrong object. The implementer
     measured this class of error in the flat design: the -O0 strict
     gate red on every stack-arg binary
     (`t3-design-notes.md`, item 3).
   - `hike_stack` base for ALL Mixed words: a reg-save-truth word
     (`off < 0`) reads/writes `hike_stack + off` — the REAL stack below
     the caller's SP, where the lifted reg-save copies do not live and
     which aliases the caller's live frame under recursion (measured:
     deep_recursion red in the WIP).
4. **The imprecise-hull case is sound too.** If a Mixed tag is merely
   an imprecise hull over a truth that never crosses the boundary, the
   select still routes each runtime word to its exact arm — soundness
   never depends on the tag's precision, only the select's condition
   does, and that condition is computed on the materialized integers
   themselves.
5. **Measured footprint:** 3 selects corpus-wide (-O0), 0 at -O2 for
   va_arg_vacopy; strict semantics 33/33 and strict opt-safety 33/33
   with them present; the -O0 models of both va_arg sources are
   SAME/SAME in the convergence report.

So: the spec's "no selects" is TRUE for the class it was written about
(the old per-tag positive/negative dispatch, whose arms were
tag-shape-dependent and partially unsound — the deleted
`rebase_addr`/`is_positive_kind`/mixed-span special case); the Mixed
select is a NEW, complete, per-word-exact rule for a class the uniform
rule cannot serve. Recommendation for the record: amend spec §T3's
letter to read "no tag-shape dispatch arms; the Mixed class
materializes through the two-base select (both arms exact)" in the
merger's commit.

## Open risks / handoff notes

1. **va_arg_vacopy's i0 grew 212→396** (the -O0 lift post-opt): the
   Mixed select + caller-lane materialization survive opt-21 (correct —
   opt-safety 33/33) but materialize more. Quality dimension only; T4
   (stack-arg promotion) is the lever that should collapse it.
2. **The Unbounded-warning binary shift** (array_local/union_overlap →
   alloca_vla/byte_copy) is benign (same class, per-sub first-hit
   artifact) but any external consumer grepping per-binary diagnostics
   should re-pin.
3. **AGENTS.md's validation block is NOT refreshed in this tree** —
   deliberate (the verdict is the record; the merger refreshes the
   block + records the provenance/bundle sha in its merge commit).
   The golden list `o2_known_failures.txt` was NOT touched (set == six;
   only its va_arg_vacopy comment line is now stale — the re-attribution
   above is the correction the merger should carry into that comment).
4. The `in_stack_segment` in-band arm's soundness rests on the
   non-canonicity argument (canonical user < 2^47; canonical kernel is
   signed-negative; `[2^61, max-int64]` intersects neither) — recorded
   here since the domain's mli states it tersely.

## Battery artifacts (home disk, `/tmp` untouched for new data)

`/home/tovpr/tm-battery/t3/`: `runtest.log`, `referee-direct.log`,
`emit-o0*/emit-o2/` (+ logs), `allocas-o0.log`, `allocas-o2.log`,
`sem-o0.log`, `semopt-o0.log`, `sem-o2.log`, `sem-o2/`, `conv.log`,
`conv-real/`. The wave-1 reference dirs were not modified.
