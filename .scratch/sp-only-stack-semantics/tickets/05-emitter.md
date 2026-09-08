# Ticket 05 — Emitter: fp_anchor deletion, lane absorption, tag-gated spills

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
