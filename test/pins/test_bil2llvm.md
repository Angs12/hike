# Pins — test_bil2llvm

Module: `test/unit/test_bil2llvm.ml` (group `bil2llvm`, ids `EMIT-01`…`EMIT-42`),
migrating `test_cbat/test_bil2llvm.ml`.  Every source `check` site is carried as
an assertion inside its family's pin; **none retired**.  Production mechanism:
`src/bil2llvm.ml` (the `emit_program` body loop and `create_sub`), the emission
lanes `src/bil2llvm_access.ml` / `src/bil2llvm_exp.ml` / `src/bil2llvm_calls.ml` /
`src/bil2llvm_env.ml`, and `src/bil2llvm_section.ml`
(`Bil2llvm.build_sections`).

No `Test_seam` switch exists for the emitter, so no switch can be
flipped from the test tier.  Production `src/` is never modified.  The disable
recipes below are textual and name the source site to break; the recorded red
is the state that recipe produces (re-demonstrated whenever the cited mechanism
changes).  Every pin builds its own fixtures inside its closure — no cross-pin
state.

Pin granularity: one pin per cohesive fixture family (the SP-RESTORE flat /
regioned twins are split; the tiling pins split per built `section_spec`), so
one failing fixture never hides the rest of the module.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| EMIT-04 | `build_entry_block` (`bil2llvm.ml`) freezes each unbound transfer var through `frozen_undef` (cached per `wvar`), so the register-file phi's entry incoming is one `%hike_undef`, never a bare `undef`. | In `bil2llvm.ml` `build_entry_block`, insert `Llvm.undef` for an unbound transfer var instead of calling `frozen_undef`. | EMIT-04 FAILs: the entry phi incoming reads `[ undef,` and no `[ %hike_undef,` is emitted. |
| EMIT-06 | `hike_ssa.ml` inserts the SP restore def at the call's single-pred continuation (`with_top_def` + `restore_word`); the emitter reads the stamped post-push version, so no SP phi and no `sp_restored` lane exist. | In `hike_ssa.ml`'s call-continuation rewrite, skip the restore def and let SP join through the IDF (add SP to the continuation's phi vars). | EMIT-06 FAILs: a ` = phi i64 ` line appears in the flat call's IR. |
| EMIT-12 | The SSA pass materializes a phi only where a var's defs meet (`hike_ssa.ml`'s `insert_phi` over the iterated frontier), and the emitter renders one incoming per (source block, exp); a duplicated rendered edge into one target does not multiply a phi. | In `hike_ssa.ml`'s `insert_phi`, append a second phi for the same lhs at the join (or in `create_elts`'s `Phi` arm, render the phi twice). | EMIT-12 FAILs: `count_two_incoming_phis` no longer returns 0. |
| EMIT-13 | `bil2llvm_exp.ml` `create_exp`'s `Var` arm answers a width-mismatched read with the frozen-undef identity — the BIR is width-honest post-coerce (ADR 0018), so the emitter coerces nothing. | In `bil2llvm_exp.ml`, reintroduce a width-coercing fallback in the `Var` arm (probe the block's other-width bindings and `Llvm.build_trunc`/`zext`). | EMIT-13 FAILs: the mismatched read emits `trunc i64 ` and no `freeze`. |
| EMIT-14 | `bil2llvm_exp.ml`'s thread-pointer lane renders the per-thread anchor and applies each access's byte offset with a GEP. | In `create_tls_ptr`, use the anchor directly without lowering the address expression's offset. | EMIT-14 FAILs: accesses at offsets 40 and 48 alias the anchor, with neither offset GEP in the IR. |
| EMIT-25 | `create_branches`'s `Direct` arm routes an `@interrupt:` target to `create_interrupt` (a `div`-trap `goto @interrupt:#0` has no block to look up). | Drop the `@interrupt:` prefix guard so `Direct tid` always calls `get_bb`. | EMIT-25 FAILs: `emit_ir` raises `Failure "bb_find_exn: @interrupt:#0"` (measured). |
| EMIT-28 | An indirect tail with no enumerated destinations is a loud failure (destination-less UB is never emitted behind a warning). | In `create_indirect_tail`, restore the warn-and-emit `indirectbr` arm. | EMIT-28 FAILs: `emit_ir` does not raise `"no enumerated destinations"`. |
| EMIT-33 | A 3+-jmp series the splitter cannot compile (not all direct gotos) reaches the emitter, which fails loudly rather than render silently. | In `create_branches`, drop the `_ ->` failwith (render nothing). | EMIT-33 FAILs: `emit_ir` does not raise `"unsplit multi-jmp"`. |
| EMIT-34 | a `Vla(T)`-origin access GEPs the `%vla` created at T (`create_dynamic_alloc` records its pair); each VLA's access hits its own alloca | drop the `Vla` arm from `mem_access` | EMIT-34 red: no `getelementptr i8, ptr %vla, i64 4` / `%vla2, i64 8` |
| EMIT-41 | `set_owner_initializer`'s `relocated_symbol` names the symbol through `Bil2llvm_env.sanitize_name`, so a slot and the call site that names the same entity agree. | Drop the `sanitize_name` application in `relocated_symbol`. | EMIT-41 FAILs: the module carries `@foo.bar` instead of `@foobar` (measured). |
| EMIT-42 | `create_branches`'s lone-jmp `Goto (Indirect …)` arm (`emit_indirect`) fails loudly on no enumerated destinations — the sibling site to EMIT-28's indirect tail. | Replace `emit_indirect`'s `failwith` with a no-op. | EMIT-42 FAILs: `emit_ir` does not raise `"no enumerated destinations"` (measured). |
| EMIT-43 | `set_owner_initializer`'s `word64` consults the loader's RELATIVE facts first: a site the `spec_relative` table names renders the fact's runtime value remapped through the sections (the same `remap_native` map every pointer load takes), never the image's raw bits. | Empty the `relative` map in `bil2llvm_section.ml` (`let _relative = Core.Map.empty (module Core.Int64)`), leaving the match arm unreachable. | EMIT-43 FAILs: the slot carries `i64 66` (the raw bits) and no `ptrtoint (ptr getelementptr inbounds (i8, ptr @text, i64 4) to i64)` (measured). |
| EMIT-44 | A word no relocation names keeps its raw bits even when they land inside a built section's span — the span never guesses an address (the class-(b) rule). | Route the unrelocated arm through `remapped_const ctx llvm_ctx llvm_module v word_ty` (the pre-rule span guess). | EMIT-44 FAILs: `i64 1288` is replaced by a remap of `@text` (measured). |
| EMIT-45 | A printable-ASCII word keeps its raw bits too: no printable-string guard and no span guess stand in the substitution rule's place. | Same disable as EMIT-44 (the span guess remaps any in-span word, string-shaped or not). | EMIT-45 FAILs: `i64 2189640` (`"Hi!"` little-endian) is replaced by a remap of `@rodata` (measured). |

**Fixture note (2026-09-29).** `emit_ir` now runs
`Hike.Cfg_complete.materialize_fallthroughs` before the split, as the
pipeline does (ADR 0024), so a fixture's guard reaches the emitter with
its false edge named.  The fixtures whose guard and fallthrough targeted
the SAME block (EMIT-01, EMIT-03, EMIT-09) now target distinct blocks —
that shape is folded to one unconditional edge by the completion, which
is the pin's point, not its subject.
