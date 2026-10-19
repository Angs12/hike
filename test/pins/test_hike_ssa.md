# Pins — test_hike_ssa

Module: `test/unit/test_hike_ssa.ml` (group `hike_ssa`, ids `SSA-01`…`SSA-13`).
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
| SSA-05 | Phis are pruned: a self-loop block gets a header phi for a var read before its redefinition (live-in) and none for a block-local temp defined then read in the same block. | In `hike_ssa.ml`'s `place_phis`, drop the `live_in` filter on the iterated frontier. | SSA-05 FAILs: the loop header carries a phi for the block-local temp. |
| SSA-06 | A call to a bodyless declaration, signed by the sign pass, reads the machine's parameter registers, so a param register defined on both arms of a diamond gets a join phi under pruning. | In `compute_sub_sig`, drop the `Model.is_declared` arm (the declaration keeps no `sig_args`). | SSA-06 FAILs: the join has no phi for the parameter register. |
| SSA-10 | The VSA on an SSA diamond binds the join phi from each edge's refined state, so every def matches the unversioned run. | In `static_graph_vsa`'s `incoming_of`, skip `bind_phis`. | SSA-07 FAILs: the phi lhs reads top and the join's reader differs. |
| SSA-11 | The VSA on an SSA loop (header phi, back edge) matches the unversioned run's value at every def. | Skip `bind_phis`, or drop the phis from `compute_need`. | SSA-08 FAILs: the counter differs from the unversioned run. |
| SSA-12 | Across an SSA call the VSA clobbers no versioned var and does not re-add the pushed word the program restores itself. | In `Cbat_forward`, pass `~pushed:true` to the call transfer. | SSA-12 FAILs: the restored SP is one word above the entry SP. |
| SSA-13 | Dead register versions are dropped at edges: after a chain of redefinitions at most the live version is held. | In `Cbat_ai_representation.gc`, drop `versioned k` from the drop test. | SSA-10 FAILs: every version of the register is held. |
