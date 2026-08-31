# Restriction Removal — VSA-Self-Seeded Stack Accesses

**Status:** spec (approved 2026-08-31; implementation NOT started)
**Tree:** `5ae223b` (② committed as `6dd9cce`) + a small UNCOMMITTED
in-flight cleanup delta in `src/` (dead-code deletions in
`calling_conventions.ml`, `convutils.ml`, `hike_kb.ml` — unused calling
conventions / helpers / the ADR-0002 arity slot; NOT part of this spec;
tree builds green with it).
**Base assumption:** the single-pass trace-partitioning fusion (ADR-0002) LANDS
FIRST; this spec is written against the fused tree, with a fallback hunk-map
for the pre-fusion tree (`edge_views_of`/`partitioned_states` still present).
**Supersedes:** T04 (`../one-frame-anchor-removal/issues/04-vsa-subsumes-relevance.md`).
**Related, untouched:** T02 (the value-tracking audit), T03 (per-call alloca for
va_list/struct-by-value).

---

## 1. Problem (the verified fact base)

The relevance pass (`src/hike_vsa_relevance.ml`) runs before the VSA and tags
defs `relevant`; `denote_def` then SKIPS every untagged def
(`src/cbat_vsa/cbat_vsa.ml:543`). The tagger is purely syntactic: its forward
pass derives SP-ness through **register defs only** — every memory
side-effect def is excluded from the propagation
(`hike_vsa_relevance.ml:126`, the `is_memory_side_effect` filter). Consequences,
all verified in source:

1. **The saved-address class is invisible.** A stack address stored to a cell
   (`mem[RBP-0x18] := RAX` where `RAX := RBP-0x30`) and later reloaded
   (`RBX := mem[RBP-0x18]`) is a value the *slice* can propagate only through
   registers — the reload's LHS is a fresh var feeding nothing tagged, so the
   deref (`RCX := mem[RBX+8]`) is never tagged and never denoted. (Stores
   through reloaded pointers ARE tagged — every store's LHS is the `mem` var,
   which every tracked Load/Store's RHS mentions — but loads through reloaded
   pointers are not.) This is the `out_variadic` / `out_va_arg_vacopy` /
   `out_nested_struct` failure class (tickets T02/T03).
2. **The call-abstraction escape lane is dead in practice.** The escape set
   reads the tracked value sets of the SysV arg registers written in the call
   block (`cbat_vsa.ml:2625-2633`); ONE top element → `escape_ranges = None` →
   `MemEnv.top` (`cbat_ai_representation.ml:372-390`) — the caller's whole
   frame dies. The arg-setup tagging that once guaranteed those defs were
   tracked (`is_arg_setup`) was DELETED by commit `31b297a` (per ADR-0001:
   "SysV arg writes are orthogonal"); the slice tags an arg def only if its
   value happens to flow to a direct stack access. AGENTS.md's L-E2 narrative
   describes the deleted code.
3. **The backward refinement lane carries hard relevance gates that AGENTS.md
   principle 2 (NO GATES) bans**: `meet_var`'s refineable check
   (`cbat_vsa.ml:1032`), `constrain_cell`'s free-vars gate (`:1041`),
   `refineable_var_of` (`:2094` — note: its comment claims "OFF → true" while
   the code is `~default:false`), and the Phase B `tag_relevant` pruning
   (`:2316-2329`, a documented ~25 s mitigation on `parse_datetime_body`).
   In production Phase B today the context is built with `refineable = None`
   (`:2337`) → every Var-operand meet is a NO-OP; only cell meets fire.
4. **The restriction buys ~nothing measurable at corpus scale:** corpus_watch
   fixpoint time is 0.0 s per binary (measured 2026-08-31 over byte_copy,
   factorial, rec_struct, array_local, variadic — all PASS, 0 crashes).
5. **The unrestricted mode is already the tested mode of the transfer
   functions:** every synthetic fixture in `test_cbat/test_cbat.ml` runs under
   `tag_all` (`:1090`) — all defs tagged. Removing the restriction changes
   wiring, not the math.

The tagger's forward SP-derivation and the VSA's frame relation
(`AI.frame` + `rewrite_addr`, in-state since WYSINWYX-2) compute the SAME
fact — which registers are frame-derived — one syntactically, one
semantically. Deleting the tagger loses nothing for direct accesses: the
frame relation already covers them inside the VSA. The saved-address class
needs value-level seeding, which only the VSA can do (WYSINWYX-3 already
represents stored frame-derived VALUES as offsets, so a tracked reload's
deref address resolves to the SAME abstract cell key as a direct access —
the representation supports the fix; the tagging was the only blocker).

## 2. Design

### 2.1 Delete the relevance restriction entirely

- The `relevant` tag, `backward_slice`, `forward_vars`, and the whole
  `hike_vsa_relevance.ml` file are DELETED. The `hike-relevance` pass
  registration (`src/hike.ml:643-647`) is DELETED; `hike-vsa`'s dep becomes
  `hike-filter`.
- `denote_def`'s gate (`cbat_vsa.ml:543`), `apply_frame_def_list`'s gate
  (`:319`), `refineable_of_sub` (`:2704`), `refineable_var_of` (`:2094`),
  the `?refineable` threading through `assume_jump_cond_with_group` /
  `assume_jump_cond` / `denote_jump` / `denote_block_with_stores` /
  `static_graph_vsa` (`:2551-2763, 2928`), `meet_var`'s refineable check
  (`:1032`), `constrain_cell`'s free-vars gate (`:1041`), `compute_need`'s
  `relevant` filter (`:2838`), and the Phase B `tag_relevant` pruning
  (`:2316-2329`) are DELETED. The walks run un-gated (Q6: yes, remove).
- Gates that always pass are dead weight, and a resurrectable gate is a
  doctrine trap. Cost control is EMPIRICAL (§5), never a gate.

### 2.2 VSA-self-seeded stack accesses — the two-channel frame-residency proof

`vsa_info.offsets` becomes the ONLY carrier of stack-access-ness (Q5). The
per-def walk in `Hike_vsa.offsets_of_sub` (and its sibling
`offsets_from_partitioned` — verify whether it is dead code; migrate or
delete) seeds a Load/Store def when EITHER channel proves the address
frame-resident:

- **Channel 1 (direct):** `rewrite_addr` (the pre-def state's frame relation)
  succeeds on the address — it is affine over frame-derived registers.
  Replaces the tagger's syntactic `is_stack_load_store` entirely. WIDENED
  frame-affine addresses still seed here: frame-residency is proven even
  when the offset range is not (`Infinite` stays a live classification —
  the big-frame fallback, sound exactly as today).
- **Channel 2 (reloaded):** `rewrite_addr` fails; denote the WHOLE address
  expression in the pre-def state; seed iff the resulting value set is
  BOUNDED and a **SUBSET of the frame neighborhood** (the offset interval
  `[−N, +M]` around the origin; N, M generous constants — the spec's
  recommendation: 64 KiB either side). WYSINWYX-3 already holds stored
  frame-derived values as offsets, so the denoted reloaded address IS the
  offset range, and `Mem.Key.of_wordset` unifies it with the direct-access
  key.

**Soundness invariant (non-negotiable): channel 2 seeds on SUBSET, never on
INTERSECTION.** A TOP, unbounded, or heap-valued reloaded address must NOT
seed (an intersect test could force a possibly-heap access into the frame
alloca — the unsound narrowing principle 5 bans). Non-seeding is the sound
raw-memory fallback. Channel 2 is bounded-only by the same argument.

The classification (`Range` / `Infinite` / `Unbounded` / `Dead` / `VLA`) is
computed from the address denotation exactly as today. The `stack_access`
tag itself is DELETED (it has no remaining meaning distinct from carrying a
`vsa_info` tag):

- `bil2llvm.ml`'s `is_stack_access` (`:744`) becomes "the def carries ANY
  `vsa_info` tag" (it already reads the map via `find_def_tag`/`def_tags_of`,
  `:713/:1761`). The 100% VSA Tagging Invariant becomes STRUCTURAL: an
  access is a stack access iff it carries `vsa_info` — the tag-vs-info
  divergence class (the va_arg poison crash) disappears by construction.
  Keep the emitter's poison path for the `Dead` classification.
- `has_stack_access_tags` (`hike_vsa.ml:63`) — the pre-fixpoint skip gate —
  is replaced by a cheap, sound prefilter: **run the fixpoint only if the sub
  has any Load/Store def at all** (no memory op anywhere → no stack access
  anywhere; the skip is safe and the common no-op sub stays free).

### 2.3 VLA detection moves into the VSA (Q11)

`detect_dynamic_alloc` relocates UNCHANGED into `cbat_vsa` (exported; the
hike-vsa pass calls it once per sub). The `dynamic_alloc` tag is DELETED
too — its only readers are the two `vla_bounds` walks in `hike_vsa.ml`
(`:245-282`, `:502-…`), which receive the tid set directly. (Conservative
alternative if the reviewer prefers tag-preserving: keep the tag, set it in
the hike-vsa pass; the detector still lives in `cbat_vsa`.)

### 2.4 Expected precision effects (predictions to verify in validation)

1. The escape lane goes live wholesale (the L-E2 restoration, no per-def
   tagging needed): every call block's arg defs are tracked, so the escape
   set reads real values; the caller frame survives calls unless a POINTER
   ARG genuinely escapes. Expect w_big / `Infinite` reductions on the
   call-heavy corpus subs.
2. Loads through reloaded stack addresses become tracked cells (the
   saved-address class); their guards' landmark acquisition fires
   (`observe_unsat_var` runs before the old refineable gate anyway —
   `cbat_vsa.ml:1028` — but the PROPAGATION past the gate was severed, and
   is now whole).
3. The 3 known semantic failures do NOT necessarily flip (Q2: removal does
   not close the class — T02's value-tracking audit and T03's per-call
   alloca remain the tickets for those), but their `Unbounded` warnings on
   frame-resident addresses should move to `Range`/`Infinite`.
4. EVERY access through a reloaded pointer that resolves into the
   neighborhood gets an offset tag; `check_allocas` counts should RISE
   (more tagged defs), and the conversion rate depends on region merging,
   not on this change.

## 3. Deletion / rewiring inventory (file:line against `5ae223b`)

| Site | Action |
|---|---|
| `src/hike_vsa_relevance.ml` (entire file) | DELETE (VLA detector moves to `cbat_vsa`) |
| `src/hike.ml:643-647` (relevance pass) | DELETE registration; `hike-vsa` dep → `hike-filter` |
| `src/hike_vsa.ml:53-60, 75` (`has_relevant_tags`, re-analyze guard) | DELETE; walk always runs |
| `src/hike_vsa.ml:62-67, 77` (`has_stack_access_tags` skip gate) | REPLACE with has-any-Load/Store prefilter |
| `src/hike_vsa.ml:99-135` (the offsets walk) | Channel 1/2 seeding replaces the `stack_access`-tag match; drop the `last_tagged` cut (walk every def; the cut existed to skip past the last tagged def) |
| `src/hike_vsa.ml:245-282, 502-…` (`vla_bounds`) | Receive the detector's tid set; tag read deleted |
| `src/cbat_vsa/cbat_vsa.ml:543` (`denote_def` gate) | DELETE — every def denoted |
| `src/cbat_vsa/cbat_vsa.ml:319` (`apply_frame_def_list` gate) | DELETE |
| `src/cbat_vsa/cbat_vsa.ml:2094` (`refineable_var_of`) | DELETE (and fix its inverted comment on the way out) |
| `src/cbat_vsa/cbat_vsa.ml:2704` (`refineable_of_sub`) | DELETE |
| `src/cbat_vsa/cbat_vsa.ml:1032, 1041` (backward-lane gates) | DELETE |
| `src/cbat_vsa/cbat_vsa.ml:2316-2329` (Phase B `tag_relevant` pruning) | DELETED by fusion; on the pre-fusion tree, DELETE here |
| `src/cbat_vsa/cbat_vsa.ml:2551-2763, 2928` (`?refineable` threading) | DELETE the parameter; `meet_var`/`constrain_cell` take no gate |
| `src/cbat_vsa/cbat_vsa.ml:2838` (`compute_need` filter) | Track every def in the SCC's value-flow cycle |
| `src/cbat_vsa/cbat_vsa_utils.ml:47` (`relevant` tag) | DELETE |
| `src/bil2llvm.ml:744` (`is_stack_access`) | Redefine: def carries any `vsa_info` tag |
| `test_cbat/test_cbat.ml:1090` (`tag_all`) + manual `stack_access` fixtures (`:5576, 6404`) | DELETE `tag_all`; REWRITE the manual-tag fixtures to exercise channels 1/2 via actual def structure, or delete if the shape is unrepresentable |
| `test_cbat/corpus_watch.ml` (`HIKE_VSA_RESTRICTION`) | DELETE the toggle + its doc line |

**Pre-fusion fallback hunk-map** (if ADR-0002's fusion has NOT landed when
this is implemented): the `?refineable` deletions apply identically, the
Phase B pruning at `:2316-2329` is deleted here instead of by fusion, and
the walk keeps `partitioned_states` for its per-def states. Nothing else
changes: the spec is deliberately invariant to the fusion order except for
these three sites.

## 4. What is deliberately NOT in this change

- **No gate resurrection under any name.** If cost forces mitigation, it is
  a measured, documented COST bound (see §5), never a soundness-adjacent
  gate.
- **No value-decided VLA upgrade** (RSP's frame term carrying fvars) — noted
  as future work only.
- **No T02/T03 work.** The 3 semantic failures keep their own tickets.
- **No probe/driver changes beyond the deletions above.**

## 5. Cost & measurement (Q3: measure-first)

The honest cost statement: removal's cost lands on **coreutils-scale subs in
the backward lane**, not the fixpoint (corpus fixpoint is 0.0 s; the one
measured pain — ~25 s — was the Phase B walk on `parse_datetime_body`, held
down by a gate this change deletes and fusion already removes).

1. **Baseline FIRST, before any deletion lands:** run the coreutils pipeline
   (103 binaries, `scripts/coreutils_pipeline.sh`) on `5ae223b`-plus-fusion,
   record per-sub wall time and the stage breakdown.
2. **Differential gate after implementation:** the same run; per-sub deltas
   reported. Budget trigger: any sub exceeding 10 s wall (or 2× its
   baseline) opens the **denotation-cheapening lane (proposal C)** with the
   measured profile naming the stage — NOT a gate.
3. **Proposal C's scope, pre-registered:** the walk's per-visit cost — the
   `meets`/`constrain_cell`/cell-denotation caches (cf. the cross-block
   cache comment at `cbat_vsa.ml:2456`) and the `refine_edge` inner
   fixpoint's `~steps:256` bound — not the transfer functions' semantics.

## 6. Validation battery (Q8: all three)

1. `dune runtest` — 0 FAIL. Expected churn: the `tag_all` deletions are
   behaviorally no-ops (all-tracked is already the fixtures' mode); the
   manual `stack_access`-tag fixtures are the REAL risk — any fixture whose
   manually-tagged access the channels would NOT seed must be rewritten to a
   seedable shape or its expectation updated (that is a test bug, not a
   spec concession; flag each in the PR).
2. Corpus: `run_corpus.sh` 32/32 rc=0; `check_allocas.sh` 0 failed (counts
   may rise — more tagged defs — the assert is 0-failed, not count-equal);
   `run_semantic.sh` 8/8; `run_semantic_all.sh` ≥ 29 PASS / 3 known FAIL
   (no regression; progress on the 3 knowns is a bonus, not a promise).
3. Precision probes: corpus_watch + precision_probe over the full corpus —
   expect exactness to MOVE UP (escape lane live; saved-address loads
   tracked). Spot-check anchors from 2026-08-31: rec_struct 96.77%,
   variadic 100.00%, sret_big 82.50%.
4. The coreutils differential of §5 — the first measured record of the
   unrestricted cost, replacing the (unrecoverable) O-series plan.
5. AGENTS.md §CURRENT VALIDATION STATE rewritten with fresh numbers and a
   fresh timestamp (per the standing directive).

## 7. Documentation state (this spec's companions, already landed)

- `docs/adr/0003-remove-restriction-vsa-seeding.md` — the ADR (supersedes
  ADR-0001's two-tag contract).
- `CONTEXT.md` — "Relevance"/"Relevance Analysis" deleted; "Stack Access"
  redefined as the two-channel frame-residency proof; the 100% invariant
  reworded structural.
- `../one-frame-anchor-removal/issues/04-vsa-subsumes-relevance.md` —
  marked SUPERSEDED.
- AGENTS.md corrections landed with this spec: the WTO fixpoint replaces the
  chunked-fixpoint text; the L-E2 narrative corrected (the tagger code was
  deleted by `31b297a`); the probe-build gap flagged; the stale "uncommitted
  ②" note fixed; the missing `docs/hike-full-plan.md` / `.slim/deepwork/`
  references marked; the `HIKE_VSA_RESTRICTION` line removed; a dated
  spot-check appended to the validation state.
