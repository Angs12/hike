# Ticket 05 — Emitter: fp_anchor deletion, lane absorption, tag-gated spills

Status: **LANDED (commit f96dbfb, merged to the PR branch as b9b4f50)** — items 1–4
done, item 5 (u32 tag-gate) deferred to T03's tags.

## Measured outcome (corrects two of this ticket's predictions)

- `dune runtest` **507 ok / 0 FAIL** — count-identical to baseline.
- -O0 corpus 32/32 rc=0; **semantic-all 32 PASS / 0 FAIL**; **semantic-opt 32 PASS /
  0 FAIL**; **check_allocas 160/0**; err streams identical 32/32; 0 unmapped
  intrinsics; zero new RBP undef-read warnings (231 both sides).
- **IR byte-identity 31/32 — item 1 is -O0-VISIBLE, not invisible as predicted.**
  Mechanism (verified in the emitted IR and the -O0 disassembly): the gcc -O0
  prologue is `push %rbp; mov %rsp,%rbp`, and BAP lifts the push as
  `mem[RSP−8] := RBP` — a READ of RBP that PRECEDES the prologue's
  `RBP := RSP` def in the same entry block. The entry binding was supplying the
  caller's RBP there; deleting it changes the stored value from a fabricated
  `anchor−8` to undef, and a global SSA renumbering follows.
  **Benign, proven by the semantic gates** (the stored slot is never read in the
  corpus) — but the ADR/AGENTS note must say item 1 is -O0-visible, and any
  future emission diff for this lane will carry that renumbering.
- **Item 2 correction: `Abi.is_callee_saved` is NOT a superset of the old
  `sp ∪ fp` test on this branch** — `callee_saved = [RBX;R12..R15]` and RBP lives
  only in the `fp` field (verified `hike_abi.ml:35`). The fp disjunct therefore
  STAYS until T06 folds RBP into the list; dropping it early would remove the
  never-defined-RBP lane that item 1 deliberately introduces.
- Callee-saved lanes (RBX/R12) **are** already threaded by `def_set` membership +
  `transfer_with_phis`; RBP threads the same way at -O0. The sp/fp disjuncts only
  govern the never-defined case.

Blocking: 04. Blocks: 06. T1 fixtures 3, 4 flip GREEN here.

## Change

1. **`build_entry_block` (`bil2llvm.ml:189-195`): DELETE the `fp := anchor−8` entry
   binding.** Never-defined RBP reads fall into the existing undef-read + `Hike_diag.warn`
   lane (the RBX treatment — `warn_undef_read` in `bil2llvm_exp.ml`). At -O0 nothing
   changes (the prologue always defines RBP before any read); at -O2 a GPR-RBP read
   no longer fabricates a frame address (T1 fixture 3 flips green).
2. **`collect_sub_data`'s SP/FP lane-keeping (`bil2llvm.ml:259-268`)**: becomes
   **sp ∪ callee_saved** (both the transfer-var set and the definedness filter).
   RBP is now an ordinary callee-saved GPR whose defs must thread block boundaries
   at -O2. VERIFY FIRST how callee-saved lanes (RBX/R12) are treated today: if they
   already thread phis, RBP inherits the same treatment by membership and the
   filter is a superset of the old sp∪fp test (RBP ⊆ callee_saved, sp unchanged)
   → -O0 identity expected. If callee-saved lanes are NOT threaded today, RBP must
   be added — otherwise -O2 GPR-RBP values die at block boundaries (the one place
   where "fp is a GPR" must be paid for honestly).
3. **`compute_sub_sig` (`bil2llvm.ml:585-594`)**: the fp test is absorbed by
   `is_callee_saved` (RBP is in the list as of T6; until T6 lands, keep the
   explicit fp test OR land T6 first if the ordering is cleaner — the filter RESULT
   must stay identical: sp, fp, and callee-saved regs are never sub params).
4. **`is_plt_trampoline` (`bil2llvm_mem.ml:38-44`)**: sp-only exclusion (drop the
   fp disjunct). A stub that genuinely uses RBP is honestly not a pure trampoline.
5. **`u32_slots_of_sub`/`cast_source_width` (`bil2llvm_calls.ml`)**: the RBP-name
   spill test → **tag-gate**: a 32-bit store is a spill slot iff its def carries a
   stack tag in `vsa_info.offsets` (the VSA proved the cell frame-resident). This
   fixes the asymmetry (RSP-based 32-bit spills were never detected) and kills
   `Abi.is_fp`'s last consumer. **The lane's one deliberate -O0 identity risk**:
   an RSP-based tagged 32-bit store could flip a sitofp width i64→i32 — the
   byte-identity gate arbitrates; if a corpus binary moves, attribute to this item
   and inspect the IR delta by hand before accepting.
6. **`Convutils.emit_ctx.fp`**: still referenced by items 1–5's old code paths —
   after the migration the field has no consumers in this ticket; its DELETION
   lands at T6 with `Abi.fp` (keep the field dead-but-present here so T6 is the
   single ABI-consistency commit).

## Gates

- `dune runtest` — the emitter wing (test_bil2llvm.ml) green; T1 fixtures 3, 4
  GREEN; the 26 FP-table rows still pinned (the cast lane changed source, not
  mapping).
- -O0 corpus IR byte-identity 32/32 — the two named risks: item 5 (tag-gated
  spills) and item 2 (lane-keeping superset). Any delta: attribute or investigate.
- Full battery; grep the corpus emissions for `unmapped intrinsic` (the FP-table
  discipline) and for `undef-read` warnings (fp_anchor's replacement lane — the
  -O0 corpus should show ZERO new RBP undef warnings; a new one means a prologue
  read precedes the prologue def — investigate).
