# Hike

Hike lifts x86-64 ELF binaries to LLVM IR, splitting the flat stack into LLVM allocas via value-set analysis over BAP BIL.

## Language

### Stack model

**Stack Access**: A Load/Store def whose address the VSA proves frame-resident: either directly (an affine address over frame-derived registers — a widened frame-affine address still counts) or through a reloaded address (a bounded value set contained in the frame neighborhood — subset, never intersect; a top or heap-valued address is not frame-resident).
_Avoid_: direct_sp, stack reference, SP-relative def, relevance tag, syntactic SP-derivation

**Frame-Residency Proof**: The VSA's own evidence that a Load/Store address lives in the stack frame — the two channels (direct affine-over-frame-derived, or a reloaded bounded subset of the frame neighborhood). The sole origin of the Stack Access classification.
_Avoid_: relevance, taint, seeding pass, syntactic SP-derivation

**Dynamic Allocation**: A definition that decrements the Stack Pointer by a non-literal size (VLA / alloca).
_Avoid_: VLA size def, runtime alloc, variable stack growth

**Stack Pointer (SP)**: The target-defined stack-pointer register (`Targetutils.sp`), the sole origin for stack-derivation.
_Avoid_: "RSP" string, RBP, frame pointer

### Analysis passes

**Library Seam** (`Hike.*`): The `hike` library's one public interface (`src/hike.mli`): `Hike.Target`, `Hike.Relevance`, `Hike.Vsa`, `Hike.Stack_to_locals`, `Hike.Kb`, `Hike.Convutils`, `Hike.Bil2llvm`. Consumers name these modules and nothing else — the entry point `Hike` is the plugin's pass pipeline, not a namespace.
_Avoid_: `Hike__X` (the dune-internal name), `Hike__.X` (the generated wrapper alias, whose resolution is unreliable)

**Stack-Access Seeding**: The VSA's classification of each Load/Store def as a Stack Access via the Frame-Residency Proof, emitted as `vsa_info` — the only carrier of stack-access-ness. No separate pass computes it.

**Trace-Partitioning (single-pass)**: Making a block's entry abstract state aware of the branch condition on its incoming edge, so the analysis is branch-sensitive rather than branch-blind; realized as one coupled pass where the deep backward walk runs inline at every conditional GOTO.
_Avoid_: Phase B, post-pass, `edge_views_of` (deleted), `partitioned_states` (deleted), `edge_view` (deleted)

**Edge-Splitting**: At a block's out-edges, computing per-edge refined successor inputs via the edge's Accumulated Condition (taken by its own cond, chain and fallthrough edges by the previous conds' negations) and transferring each to its destination block.
_Avoid_: edge view, branch partition, taken/fallthrough views (the old per-edge Phase B record)

**Accumulated Condition**: The per-edge path condition BAP's IR graph computes (`Graphs.Ir.Edge.cond`): the edge's own guard conjoined with the negation of every preceding when-guard in the same block — including on unconditional chain-tail gotos.
_Avoid_: chain side-conditions, path predicate, the jmp's own cond

**Inverse Denotation (Deep Walk)**: The backward derivation of a block's pre-state from a post-edge constraint, via producer subtraction (`cstr' = cstr ∩ post(v)`) and trace-exact cell meets; what `refine_edge` computes inline at each jump.
_Avoid_: inverse_denote_exp (the shallow production no-op), guard-meet-only

**TAG State**: A per-block abstract state already refined by its incoming edge conditions; in the single-pass design this is simply the block's IN-state in the VSA solution.
_Avoid_: partitioned state, per-edge view

**100% VSA Tagging Invariant (structural)**: A Load/Store def is a Stack Access iff it carries a `vsa_info` tag (`Range`, `Infinite`, `Unbounded`, `Dead`, or `VLA`). The classification is one mechanism — there is no second tag to diverge from it.

### Mem-fission

**Region Mem** (`stack_rN_mem`): the per-region BIL memory var every fissioned access reads/writes — the storage decision carried in the BIL itself. Recognized by name (the fission convention), routed to the region's alloca, and swept by the load-roots DCE rule: a region's stores survive iff some Load reads its var.
_Avoid_: arr_of (the deleted pre-fission name), tag-consultation at emission

**Region Base** (`stack_rN_base`): the region's cell-0 address var, entry-bound to the alloca; the fissioned address `[base + index]` keeps the original index arithmetic with the base naming the region. Both operands of a fissioned access name the region — a split storage (one path's alloca GEP vs another's raw lane for the same cell) is unrepresentable.
_Avoid_: sp-lane arithmetic for fissioned members

### VSA Classifications

**Range**: A bounded stack offset interval `[lo, hi]` where `lo` and `hi` are known integers.
**Infinite**: A widened stack offset interval `[lo, hi]` where one or both bounds represent unbounded growth.
**Unbounded**: A stack access whose address value set is completely unconstrained (`TOP`), spanning the whole stack frame.
**Dead**: A stack access on an unreachable execution path (`BOTTOM`), eliminated by DCE.
**VLA**: A stack access targeting a dynamic allocation frame.
