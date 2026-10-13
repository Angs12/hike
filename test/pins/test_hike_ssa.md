# Pins — test_hike_ssa

Module: `test/unit/test_hike_ssa.ml` (group `hike_ssa`, ids `SSA-01`…`SSA-05`).
Production mechanism: `src/hike_ssa.ml` (the `hike-ssa` pass) plus the
emitter's SSA reading (`bil2llvm_env.ml`'s version stamps and sub-wide
bindings; `bil2llvm_calls.ml`'s `bind_call_ret`).

Fixtures are hand-built BIR signed through the real `sign_program` +
`ssa_program` pair.  `emit_ir` (fixtures.ml) runs the same pipeline the
production chain runs: types → split → ssa → emit; the emitter pins
(EMIT-*) therefore exercise the SSA BIR end to end.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| SSA-01 | Each call site's ret lanes mint fresh versions; the block's `Versions.rets` stamp carries them, and the continuation's read of the ret base resolves to the minted version. | In `hike_ssa.ml`'s walk, empty the `minted` list before stamping (never version the ret lanes). | SSA-01 FAILs: no `RAX` entry with index > 0 in the stamp, and the continuation still reads the base var. |
| SSA-02 | A join where a var's two defs meet materializes a phi: versioned lhs, two incoming exps (one per source block), each naming the source's def version. | In `iterated_frontier`'s consumer, skip the `Term.append phi_t` (place no phi). | SSA-02 FAILs: the join block has no `sj_v` phi (or an unversioned lhs / wrong incoming count). |
| SSA-03 | Under SSA the sub's input lanes are its index-0 reads (`free_regs_ssa`); `is_ssa` marks the sub. | In `free_regs_ssa`, drop the `Var.index v = 0` filter. | SSA-03 FAILs: the versioned def lhs joins the input set. |
| SSA-04 | Call return mints are definition sites for iterated-frontier phi placement, so the call result and bypass value meet at their join. | In `hike_ssa.ml`, place phi sites only at blocks with BIR defs and phis, omitting call return mints. | SSA-04 FAILs: the join has no versioned `RAX` phi carrying the call's return version. |
| SSA-05 | A dynamic-allocation def records the SP version live before it (`Def_slots.def_sp_before`), though its rhs reads no SP and its lhs is another register; the emitter sizes the alloca from that version. | In `hike_ssa.ml`'s walk, stamp `top (Def.lhs d)` instead of `top sp`. | SSA-05 FAILs: the stamp is the producer register's previous version, not the SP version the preceding adjust defines. |
