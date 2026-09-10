# S10 — the post-T4 simplification wave (ticket DRAFT, audited 2026-09-10)

Audit basis: `typed-model-program` @ `19c41a5` (T3c-landed) + the T4
WIP diff (`tm/t4-stack-args`, 15 files, +788/−290) for conflict
classification. Execute AFTER T4 merges; reconcile this draft against
T4's verdict retirement inventory at the merge.

## 0. What T4's in-flight tree already resolves — do NOT re-propose

The T4 WIP (verified by diff) already lands: the **servability clause
deleted** (`unservable_stack_traffic` gone; `regions_of_sub` drops
`~sol`, purely geometric), the **`hike_stack` → `hike_window` rename**
(`hike_window_var`), the **`llvm.stacksave` bridge and both T3
SP-binding arms retired** (the SP Slot), the **`has_positive`
Caller/Mixed signature test replaced** by `prom_window`/`prom_arity`,
**`denote_imm_exp` + `relativize_opt` promoted to the production
surface** of `cbat_vsa.mli`, `prom_*` + `call_site` + `thunks` added to
the record, and `restore_sp_after_call`/`edge_sp_restores` **KEPT**
(correctly: a mid-frame call's post-call SP is call-block SP + 8, not
the slot's entry anchor — the slot does not subsume it; audit answer,
not a candidate). `hike_stack_to_locals.ml` and `hike_dce.ml` are
**untouched by T4** — the mem-fission vocabulary and DCE's load-roots
rule survive the promotion intact. The pass pipeline needs no merge
under the SP Slot.

## 1. Ranked candidate table

| # | Candidate | Where | Size | Doctrine class | Conflict | IR re-baseline? |
|---|---|---|---|---|---|---|
| 1 | Dead: `is_abi_visible` wrapper + `abi_visibility_of` — the emitter's last abi-visible consult died with T3's uniform materialization; zero callers for the wrapper; keep `is_abi_visible ~tag_of` (STL uses it) | `src/bil2llvm_mem.ml:18-19`, `src/hike_stack_model.ml:248-250` | S | dead weight | safe | no |
| 2 | Dead: `store_data_exp_of_rhs` — zero refs outside its def; the wrapper twin `store_data_of_rhs` is the consumed one | `src/hike_stack_model.ml:34-44` | S | dead weight | safe | no |
| 3 | Probe `width_diag` — one-shot L1 diagnostic; the width contract is enforced at `create_def` birth since L1. A probe with no remaining question is deleted like dead code. Keep `dead_diag` (the Dead warn class persists) | `zz_scratch_probe/width_diag.ml` + stanza | S | dead weight | safe | no |
| 4 | Probe `escape_diag` — it IS T4's acceptance instrument (the 21-sub recovery measurement); post-verdict it has no caller. Delete (or rename `region_diag` dropping the stale `escape=` labels) in the wave, not before | `zz_scratch_probe/escape_diag.ml` + stanza | S | dead weight | safe **after T4's verdict** | no |
| 5 | Stale-comment batch naming deleted/renamed machinery: `cbat_vsa.mli:92-95` ("denotational escape rule"); `cbat_vsa.ml:610-612` ("the hike_stack lane"); `hike_stack_model.ml:349-351` (frame_dims Mixed arm); `hike_dce.ml:114-118` ("SP local binds to hike_stack"); `cbat_vsa.ml:631-632` (relevance-pass provenance clause); the 12-blank-line block at `bil2llvm.ml:299-311`; fragment at `bil2llvm_calls.ml:78-81`. Doc debt: AGENTS.md's debug-executable list omits `dead_diag`/`width_diag`/`escape_diag` | as listed | S | dead weight | safe | no |
| 6 | **The guard-decoder store-chain** (T3c's flagged ~120 lines, concretely): `prove_nonneg` (`cbat_walk.ml:164-282`) + `known_nonneg_of` (285-289) + the `~known_nonneg` threading + `analysis_ctx.stores`/`?stores` plumbing. The replacement is T3c's measured-and-reverted denotational test; its L-D2/L-D6 reds exist because the flat denotation at the guard does not carry the cell bound. **T4 does not change this — T5's same-iteration producer subtraction + the `def_constraints` Store row is exactly what enriches the guard-point denotation.** Re-attempt POST-T5, measured-only, inventory-first | `src/cbat_vsa/cbat_walk.ml:164-289` + threading | M | mechanism removal (the ONE-mechanism doctrine's last named exception) | **T5** (semantic; textual overlap low) | possibly (guard-refinement precision moves) |
| 7 | Post-T4 `denote_def`/`denote_defs` surface check: promoted for T3c's servability clause, which T4 deletes — demote any orphaned member back to `Test_seam`. Verify at T4 merge; one-line mli change | `src/cbat_vsa/cbat_vsa.mli:96-98` | S | surface honesty | safe | no |
| 8 | **The region-GEP lane + the precise-sub materialization audit** (measurement, not a deletion): T4's WIP makes the region arm load-bearing (the SP Slot anchors to the first region alloca for precise subs). In a precise sub `typed_frame` is `None`, so non-singleton Range/Infinite accesses flow `create_exp → create_addr_ptr → inttoptr` over SP-slot-derived integers — the T1 class ("right runtime value, wrong/no underlying object"). Verify opt-safety holds; a violation spawns a fix ticket, never a rider | `src/bil2llvm_mem.ml:291-306`, `src/bil2llvm_section.ml:138-157` | M (measurement; L if a fix spawns) | verification | safe (run on T4's own battery artifacts) | only if a fix lands |
| 9 | **The convutils split** (the 2026-09-09 review's future lane — overdue): T4 grows the drawer to (a) the Vsa record, (b) emitter state (`emit_ctx` + `thunks` + the WVar/phi/local machinery), (c) sig/ABI helpers, (d) BAP misc, (e) section types, (f) the window var. Proposal: the record module out (or folded into `Hike_stack_model`); `emit_ctx` + llval maps into `Bil2llvm_env`; the residue dissolves. Behavior-identical module move; var names (the only IR-visible surface) unchanged | `src/convutils.ml` (334→~430 post-T4), ~16 fixture call sites | M/L | architecture | **T4** (run first in the wave, before T5/T9 branch) | no |
| 10 | Model tidies: co-locate var factories (window var + slot vars) in `Hike_stack_model` or accept and document the model as the var-grammar home. `regions_of_sub`/`split_plan`'s home is still right | `src/hike_stack_model.ml` | S | architecture/cosmetic | safe | no |
| 11 | `hike_vsa.ml` post-T4 (~78 → ~390 lines): if T4's final shape keeps the promotion classifier + tag extraction + the plan fold together, split the promotion classifier out post-T4 | `src/hike_vsa.ml` | M | architecture | safe (post-T4) | no |
| 12 | **Post-T9 residue sweep** (pre-registered so T9's acceptance greps are complete): when the window retires — `hike_window_var`, `caller_mem_access`, `mixed_mem_access` (near-duplicates; fold any survivor onto `mem_access_at_ptr`, no one-caller wrappers), `prom_window`, the `Mixed` PRODUCTION arms (the enum row may survive as classify output for non-window traffic — verify before deleting the kind) | `src/bil2llvm_mem.ml:129-182`, `src/convutils.ml`, `src/hike_stack_model.ml`, `src/cbat_vsa/cbat_vsa.ml` | M | mechanism removal | **T9** | yes (deliberate, with T9's verdict) |

**Explicitly NOT candidates (recorded not-done, re-confirmed):**
`create_branches`' >2-branch failwith; `Clp.compare` (interface-forced);
the wordset_intf shrink (re-verified test-used); the `simplify_jmps`
removal (TID renumbering = deliberate-re-baseline class, never a
rider); the `Cbat_vsa_stages` debug/prod adapter seam (rule 6's
sanctioned mechanism); `dead_diag`; `restore_sp_after_call`/
`edge_sp_restores` (not subsumed by the SP Slot — mid-frame calls).

## 2. Lane order

1. **Gate at T4 merge**: reconcile this draft against T4's verdict
   retirement inventory (items 4, 7 resolve there).
2. **S10a — dead weight + stale comments** (items 1-5, 7, 10):
   acceptance = `dune runtest` failure set unchanged, referee 0,
   corpus emission **byte-identical 37/37** both lanes, all semantic
   gates green. Carries the AGENTS.md probe-list doc fix and the
   region-GEP/inttoptr MEASUREMENT (item 8) as an observation
   deliverable on T4's battery artifacts — a violation spawns its own
   ticket (inventory-first).
3. **S10b — the convutils split** (items 9, then 11):
   behavior-identical module moves; IR byte-identity asserted; lands
   BEFORE T5/T9 branch.
4. **T5** (program schedule, unchanged). T5's verdict measures the
   denotational `known_nonneg` replacement as a side observation (the
   S10c disposition comes free).
5. **S10c — post-T5, measured: the store-chain deletion** (item 6).
   Red → the chain stays, the inventory grows one line; green → the
   ~130 lines delete with the mechanism named.
6. **T9** (program schedule), then **S10d — the window/Mixed residue
   sweep** (item 12) with T9's verdict.

## 3. Guidance for T5/T9

- **T5**: no emitter change required (the design notes hold). T5's
  guard-point enrichment is the PRECONDITION for deleting the
  store-chain — measure the denotational replacement in T5's verdict.
- **T9**: acceptance greps include `hike_window`, `caller_mem_access`,
  `mixed_mem_access`, `prom_window`, and the Mixed production arms —
  not just "no window parameter in signatures". Fold surviving
  dispatch onto `mem_access_at_ptr`; verify the `Mixed` kind's classify
  outputs before deleting the enum row.
- **Both**: consume promoted facts through the record (`prom_*`),
  never re-derive — the one-mechanism conformance grep the wave runs
  over their diffs.

Tooling note: the system `grep` is ugrep 7.8.4 — its `-w` does not
treat `_` as a word character and its recursive search silently returns
nothing with `2>/dev/null`; dead-binding scans must use plain
fixed-string greps (items 1-2 verified to exactly one occurrence: the
definition).
