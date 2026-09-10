# S10a — verdict: the dead-weight + stale-comment wave, and the region-GEP measurement

Landed 2026-09-10 on `tm/s10a` (worktree `/home/tovpr/hike-s10a`), branched
at the T4b-merged tip `e723f09`. Commits: `5db5c82` (items 1+2+10),
`42e7882` (items 3+4 + the AGENTS.md list), `8c5c303` (items 5+7).
Final provenance: `src=49700c5eb37ff5a6` `bundle=0b656a00ab72d298`
(recorded post-commit; the src hash is the battery-run content's hash —
identical). Battery artifacts: `/home/tovpr/tm-battery/s10a/`.

**ZERO behavior change, proven: corpus emission BYTE-IDENTICAL 37/37 on
BOTH lanes** vs the T4b references `/home/tovpr/tm-battery/merge-t4b/
emit-{o0,o2}` (`cmp` per file, out_*.ll and err_*.txt both — 0 diffs
of 37 + 37 + the stderr sets).

## 1. Deletion inventory (every deletion with its no-caller proof)

Proofs are plain fixed-string greps over `src/ test_cbat/
zz_scratch_probe/ scripts/` (the system grep is ugrep — no `-w`, no
`2>/dev/null` recursion, per the S10 tooling note).

| item | deleted | proof |
|---|---|---|
| 1 | `Bil2llvm_mem.is_abi_visible` (the sub_info wrapper) | fixed-string `is_abi_visible` over all consumers: only its own def; the emitter never calls it (the last consult died with T3's uniform materialization) |
| 1 | `Hike_stack_model.abi_visibility_of` | consumed only by the wrapper above; both die together |
| 1 | KEPT: `Hike_stack_model.is_abi_visible ~tag_of` | `hike_stack_to_locals.ml:16,52` consumes it (`Model.is_abi_visible ~tag_of`) |
| 2 | `Hike_stack_model.store_data_exp_of_rhs` | fixed-string: exactly one occurrence — the definition. The consumed twin `store_data_of_rhs` (hike_vsa's outgoing-slot map) stays |
| 3 | probe `width_diag.ml` + its dune stanza | references: its own file, its stanza, and AGENTS.md's historical validation block (owner's record, untouched). The width contract is enforced at `create_def` birth since L1. `dead_diag` KEPT (the Dead warn class persists — ticket's explicit keep) |
| 4 | probe `escape_diag.ml` → **renamed `region_diag.ml`** (not deleted) | the probe's core content is the live instrument for the region/materialization lane (per-call-block pointer-arg denotations + the region plan + the singleton census — exactly the dig tools T5/T9 class work needs); only the VOCABULARY was stale. Dropped: the `escape=%b` labels (now `stack=%b` — they always printed the stack-symbolic bit), the "escape veto OFF" comment (now describes the extraction-to-plan flow), and the usage string. Its `Vsa.denote_defs` call moved to `Vsa.Test_seam.denote_defs` with item 7 |
| 5 | comments (see §2) | per-site |
| 7 | `val denote_defs` on the production surface of `cbat_vsa.mli` | see §3 |

Net: 11 files, +41/−133 before the verdict.

## 2. Item 5 — the stale-comment batch, per-site disposition

| S10 audit site | found in the landed tree | action |
|---|---|---|
| `cbat_vsa.mli:92-95` ("denotational escape rule") | present (T3c rationale for the denote surface) | rewritten — `denote_def`'s comment now names the real production consumer (hike_vsa's outgoing-slot map); the escape-rule sentence is gone (§3) |
| `cbat_vsa.ml:610-612` ("the hike_stack lane") | T4's landing had already rewritten it to "the caller-window lane (T4: renamed from hike_stack)" | trimmed the dead-name parenthetical — the lane name is the caller-window lane, full stop |
| `hike_stack_model.ml:349-351` (frame_dims) | found as a DUPLICATED function header: the pre-T4 comment block sitting directly above its T4-updated replacement | the superseded first block deleted; one comment remains |
| `hike_dce.ml:114-118` ("SP local binds to hike_stack") | already modernized by T4's landing ("since T4 the SP local binds to the sub's own SP Slot") | nothing to do — verified in-tree |
| `cbat_vsa.ml:631-632` (relevance-pass provenance) | present ("relocated unchanged from the deleted relevance pass (spec §2.3)") | trimmed to what `detect_dynamic_alloc` IS ("Runtime-sized SP decrements (the VLA matcher)"); the dead pass and the dead spec reference are gone |
| `bil2llvm.ml:299-311` (12-blank-line block) | the block itself died with T4's landing; the last trace was one trailing-whitespace line at `create_sub` | the whitespace line removed |
| `bil2llvm_calls.ml:78-81` (fragment) | present at `:108` — the orphaned `(* Sub declarations ... *)` header + blank padding mid-file | deleted (the declarations live elsewhere) |
| AGENTS.md debug-executable list omits `dead_diag`/`width_diag`/`escape_diag` | confirmed | **the sanctioned list fix only**: the list gains `region_diag.exe` (with the rename provenance) and `dead_diag.exe`; `width_diag` was never listed — its deletion resolves that omission. Validation blocks untouched (owner's) |

Two live `hike_stack` dead names in `bil2llvm.ml`'s comments (the SP-Slot
"retired" sentence and the signature lane's "renamed from hike_stack")
also trimmed — deleted machinery is not re-narrated.

## 3. Item 7 — the denote_def/denote_defs surface check

T4 deleted T3c's servability clause (the promotion rationale). Verified
against the landed tree:

- **`denote_def` STAYS on the production surface.** Production src
  consumers: `src/hike_vsa.ml:201` (the block walk denoting defs to the
  call point) and `:221` (the outgoing-slot map denoting each storing
  def to read the slot's store-time SP offset). Not orphaned — demoting
  it would break the promotion classifier.
- **`denote_defs` DEMOTED.** No production src consumer: the only
  in-library caller (`cbat_walk.ml:1789`) reaches `Cbat_transfer`
  directly through `open Cbat_transfer` — the mli surface name was
  orphaned by T4; tests already go through `Test_seam` (which
  re-exports it); the renamed probe follows them. The top-level
  `val denote_defs` is deleted; the `Test_seam` member remains.

## 4. Item 10 — the var-grammar home (co-location landed)

`hike_window_var` moved from `convutils.ml` to `Hike_stack_model.ml`,
next to `slot_of`/`arg_slot`/`region_mem`/`region_base`: **the model
owns the var grammar** — window, slots, and regions all mint there.
The 13 emitter references re-pathed `Convutils.→ Hike_stack_model.`;
the minted name `"hike_window"` is untouched (the only IR-visible
surface is the name — byte-identity proves the move is emission-neutral).
Documented acceptances: the emitter's `hike_acc` marker stays in
`bil2llvm_mem.ml` (emitter-internal lane plumbing, never model
vocabulary), and the `intrinsic:xN` temps are BAP's grammar, not ours.

## 5. Item 8 — THE MEASUREMENT: the region-GEP question answered

**Question.** In precise subs (`typed_frame = None`), do non-singleton
Range/Infinite accesses flow `create_exp → create_addr_ptr → inttoptr`
over SP-slot-derived integers — the T1 class (right runtime value,
wrong/no underlying object)?

**Code-path answer (static, this tree).** The dispatch CAN reach it:
`create_def` sets `frame_wrap_license := true` for every
Range/Infinite def; a precise sub has `typed_frame := None`; so a
non-singleton tagged access there goes `mem_access` (Range/Infinite
arm) `→ create_exp → create_load/create_store → create_addr_ptr →
match (None, true) → _ arm = inttoptr`. The hole exists in the code.

**Empirical answer (on T4b's own artifacts, byte-confirmed identical to
this lane's fresh emissions).** IT DOES NOT FIRE — zero occurrences,
both lanes:

| lane | precise subs (stack_r allocas, no %frame) | inttoptr of ANY kind in them | sp_slot-derived inttoptr |
|---|---|---|---|
| -O0 (`merge-t4b/emit-o0`) | 42 | **0** | **0** |
| -O2 (`merge-t4b/emit-o2`) | 8 with region bases (21 by alloca presence) | 5, all foreign | **0** |

Method: per-function SSA census over every `out_*.ll` — all inttoptr
occurrences collected, each traced transitively through defs (phis
included) to test derivation from the SP-slot load (`%stack_0 = load
i64, ptr %sp_slot`).

- -O0: the 42 precise subs emit 911 region-base binds and **no memory
  access rooted at anything but regions** — actually the corpus's
  precise subs carry no direct cell traffic at all (promotion removed
  it; the region-base binds are the anchor plumbing). ALL real cell
  traffic (1,908 load/store accesses) is rooted at `%frame` — those
  subs are Frame-JOINED, and their tagged accesses materialize through
  `create_addr_ptr`'s LICENSED GEP arm (`frame + (word − anchor_i64) +
  anchor_idx`), which is the T1-FIXED form: right runtime value AND the
  right underlying object. 236 accesses are the `%sp_slot` anchor
  round-trip itself; 190 are the by-design foreign lanes (window/Mixed
  inttoptr over the window parameter, section loads, VLAs).
- -O2: the 5 inttoptr in region-carrying subs are RELOADED FOREIGN
  pointers — fizzBuzz ×4 over `load i64, ptr @bss` (the reloaded-
  pointer exception lane) and jump_table_sw's jump-table dispatch
  address (`add %243, %257` over a section constant). None SP-derived.
- Strict opt-safety is 37/37 PASS on the same artifacts (T4b's
  `semopt-o0` and this lane's re-run) — the gate's verdict corroborates.

**Verdict: no violation, no fix ticket.** Two structural reasons the
unreached arm is safe BY CONSTRUCTION, not by luck: (1) inttoptr claims
NO basedness — it is provenance-erasing, the exact OPPOSITE of the T1
regression (the GEP falsely claiming frame residency); an optimizer
cannot delete or relocate what it cannot attribute. (2) The SP slot's
value is `ptrtoint(stack_r0)`, so a hypothetical `inttoptr(sp0 + off)`
would have the exact runtime value AND a real underlying object (the
region alloca) — it would merely be INVISIBLE to the optimizer, costing
convergence, never correctness. If a future corpus shape ever reaches
that arm, the disposition is a precision note (route the ranged access
to its region GEP), never a correctness ticket. Recorded here so the
next corpus growth checks this census again.

## 6. Gate table (the final tree)

| gate | result |
|---|---|
| build, default + vsa-debug profiles | rc=0 both (post-recovery rebuild re-verified) ✅ |
| instrumentation blocker | clean (exercised by both builds) ✅ |
| `dune runtest` failure set | **== EXACTLY the 8 pre-existing** (E2eD-7/8, LM F1-B1×2, F1-B3, F1-FT×2, F1-NEQ) — set-level `diff` vs T4b's runtest.log: IDENTICAL ✅ |
| forced rerun (`dune runtest --force`) | referee **clpequiv: checked=2,861,148 mismatches=0** (the battery's log elided the cached pass; forced log: `runtest-forced.log`) ✅ |
| -O0 emission | 37/37 rc=0 ✅ |
| -O0 structural asserts | 185 passed, 0 failed ✅ |
| **-O0 emission byte-identity vs `merge-t4b/emit-o0`** | **37/37 IDENTICAL** (out_*.ll; err_*.txt identical too) ✅ |
| -O0 strict semantics | **37 PASS / 0 FAIL** ✅ |
| -O0 strict opt-safety | **37 PASS / 0 FAIL** ✅ |
| -O2 emission | 37/37 rc=0 ✅ |
| -O2 structural asserts | 185 passed, 0 failed ✅ |
| **-O2 emission byte-identity vs `merge-t4b/emit-o2`** | **37/37 IDENTICAL** ✅ |
| -O2 pinned semantics | **semantic-pin: OK — failing set == golden list (7 knowns)**; no movement ✅ |
| provenance | src `49700c5eb37ff5a6`, bundle `0b656a00ab72d298` ✅ |

Battery summary: the single hard red is the `dune runtest` rc gate — the
pre-existing 8-failure baseline makes `dune runtest` exit non-zero by
design; T4b's own battery record shows the identical red
(`merge-t4b/battery-t4b-merge.summary`). Everything else green, and the
lane's own acceptance (failure set unchanged, referee 0, byte-identical
37/37 both lanes, semantics green) holds.

## 7. Not done here (by scope)

- Item 6 (the guard-decoder store-chain) — S10c, post-T5.
- Items 9/11 (the convutils split, hike_vsa split) — S10b. Note: item
  10's move took one var OUT of convutils ahead of S10b; `hike_window_var`
  now lives where S10b's record-module fold would put it.
- Item 12 — S10d, post-T9.
