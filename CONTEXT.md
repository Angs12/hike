# Hike

Hike lifts x86-64 ELF binaries to LLVM IR, splitting the flat stack into LLVM allocas via value-set analysis over BAP BIL.

## Language

### Stack model

**Stack Access**: A Load/Store def whose address's DENOTATION is a stack-symbolic set inside the segment — the one predicate (`is_stack_access` over the denotation). No second channel, no seed flags, no syntactic derivation.
_Avoid_: direct_sp, stack reference, SP-relative def, relevance tag, SP-derived closure, is_seed, two channels

**Symbolic Stack Base** (`stack_0`): The entry SP's word, seeded with the bounded segment; arithmetic propagates the symbol, bitwise/compares go TOP-unknown. The ONE mechanism: it finds stack accesses, resolves call targets, and answers every producer question the escape analysis used to approximate — the escape fact is deleted, its consumers read the denotations directly.
_Avoid_: escape analysis, frame escape fact, seeded flag, frame relation

**Dynamic Allocation**: A definition that decrements the Stack Pointer by a non-literal size (VLA / alloca).
_Avoid_: VLA size def, runtime alloc, variable stack growth

**Stack Pointer (SP)**: The target-defined stack-pointer register (`Abi.sp`), the sole origin for stack-derivation and the only register granted stack semantics by fiat.
_Avoid_: "RSP" string, RBP, frame pointer

**Frame Pointer (FP)**: The target's frame-pointer register — an ordinary callee-saved GPR carrying no stack semantics by name. Its stack-ness, like any register's, is proven: by a frame term (an sp-derived value) or by the SP-seeded derived closure. Never assumed.
_Avoid_: fp-as-stack-register, is_stack_reg, RBP-by-name, frame-pointer grant

### Analysis passes

**Library Seam** (`Hike.*`): The `hike` library's one public interface (`src/hike.mli`): `Hike.Abi`, `Hike.Vsa`, `Hike.Dce`, `Hike.Stack_model`, `Hike.Stack_to_locals`, `Hike.Kb`, `Hike.Convutils`, `Hike.Bil2llvm`. Consumers name these modules and nothing else — the entry point `Hike` is the plugin's pass pipeline, not a namespace.
_Avoid_: `Hike__X` (the dune-internal name), `Hike__.X` (the generated wrapper alias, whose resolution is unreliable)

**Test Seam** (`Cbat_vsa.Test_seam`): The quarantined module carrying every vendored-VSA name consumed only by test_cbat and the probes (the walk internals, assume/refine/denote, the fixtures' constraint grammar, `mk_rctx`/`walk_budget`). Production `src/` consumes the interface above it and nothing in the seam; a name in the seam must never leak into a production signature.
_Avoid_: test-only exports in the production interface, the pass-through re-export block (deleted)

**Stack-Access Seeding**: The VSA's classification of each Load/Store def as a Stack Access via the Frame-Residency Proof, emitted as `vsa_info` — the only carrier of stack-access-ness. No separate pass computes it. `vsa_info` carries per-def offset ranges — the possible range of each access — and nothing else; every other producer question (does the frame escape?) is a fact, not a tag.

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

### Autonomy

**Autonomous Pass**: A pass that consumes its predecessor's output as authoritative and performs only its own algorithm — it may find nodes, dispatch on node kind, apply record-driven rules, and compute facts about its own output; it may not re-derive any producer fact (stack-ness, address shape, escape, region membership).
_Avoid_: defensive pass, re-validation, belt-and-braces, distrust guard

**Guard**: A conditional refusal that distrusts a computed fact — a check whose premise is that a producer's output may be wrong. Banned: the construction is made correct instead.
_Avoid_: gate, sanity check, refusal-to-refine, conservative refusal

**Rule**: An unconditional mapping from a fact to an action — the sound fallback for a domain value (Unbounded → dynamic emission, Dead → poison) is a rule, not a guard.
_Avoid_: fallback check, safe path

**Stack Member**: The per-def entry in `vsa_info` that carries the analysis facts (kind, span, address, base, storage requirement, sp-mention) — the unit the partition joins.
_Avoid_: tagged def, region candidate, conversion candidate

**Overlap Partition**: The stack model's sole soundness mechanism: members join into connected components of the interval-overlap graph; each component's storage class is the join of its members'; the join decides Static (region alloca), Frame (the model frame — the sound fallback storage), Dynamic (runtime alloca), or Dead.
_Avoid_: gate battery, split-plan checks, convertibility gate

**Storage Class**: The lattice a partition component joins to — Static, Frame, Dynamic, or Dead (identity). `Static ⊔ Frame = Frame`, `Frame ⊔ anything = Frame`, `Static ⊔ Dynamic = Dynamic` (one merged runtime alloca).

**Frame Dims**: The frame geometry facts (deepest extent, span) as record payload — consumers read them instead of re-folding tags.

### Traversal

**Visitor-Only Traversal**: Walking or mapping defs/terms/exps uses the BAP visitor/mapper combinators, never hand-rolled structural recursion. Single-node kind tests (a value's kind) are sanctioned; the emitter's total exp dispatch is exempt.
_Avoid_: AST pattern matching (for traversal), hand-rolled recursion

**Kind Test**: A single-node dispatch on a term or exp's constructor (Jmp.kind, Call.target, Blk.elts) used to decide its kind — sanctioned; not traversal.
_Avoid_: structural match (ambiguous with banned traversal)

### Emitter

**Emission Entry (`emit_program`)**: The emitter's single public operation: given a program term and the target-derived facts (target, pointer size, symbol table, text section, section remap, copy relocations, section list), it populates the emitter state and performs both internal passes — signature collection (the sub declarations) and body emission. Output is the side effect on the caller-owned LLVM module.
_Avoid_: `create_prog` (the pre-seam name), `init_subs` (the caller-side pre-seam two-pass protocol), reaching the emitter's KB context vars from outside

### Mem-fission

**Region Mem** (`stack_rN_mem`): the per-region BIL memory var every fissioned access reads/writes — the storage decision carried in the BIL itself. Recognized by name (the fission convention), routed to the region's alloca, and swept by the load-roots DCE rule: a region's stores survive iff some Load reads its var.
_Avoid_: arr_of (the deleted pre-fission name), tag-consultation at emission

**Region Base** (`stack_rN_base`): the region's cell-0 address var, entry-bound to the alloca; the fissioned address `[base + index]` keeps the original index arithmetic with the base naming the region. Both operands of a fissioned access name the region — a split storage (one path's alloca GEP vs another's raw lane for the same cell) is unrepresentable.
_Avoid_: sp-lane arithmetic for fissioned members

**Stack-Arg Promotion**: The total conversion of stack-passed call arguments to real call parameters — the callee's proven incoming stack slots become parameters; callers' outgoing stores become call arguments at every resolved site. Per-slot mixing (unprovable slots stay on the window); per-slot width rule (promoted at the stored width, narrower reads truncate, a wider read demotes the slot).
_Avoid_: outgoing-area threading, memory-passed args, provenness gate

**SP Slot**: The entry-block alloca every memory-touching sub owns, holding the sub's per-invocation stack anchor (the ptrtoint of its own frame or region storage). SP is never a function parameter; model SP mutations are stores to the slot.
_Avoid_: hike_stack parameter, threaded SP, SP argument

**Per-Invocation Anchor** (`stack_0`): The model's stack origin, bound at entry to the sub's own storage base — reentrant-safe; SP-relative offsets are frame-relative. No constant anchor, no shared region.
_Avoid_: constant anchor, global stack base

**Resolved Call Site**: A call site whose target the VSA proves a singleton lifted sub — it emits a direct call through the target's promoted signature. A bounded multi-target set or any foreign address emits the pointer call (memory convention).
_Avoid_: synthetic indirect signature, indirect-call heuristic

**Thunk** (memory-convention twin): The twin of an address-taken promoted sub, carrying the legacy memory-path signature; function-pointer data renders to the thunk, so unresolvable call sites stay sound through the pointer.
_Avoid_: trampoline, target demotion

**Caller-Window Parameter**: The residual window-base parameter — variadic subs (bridge until the va_list re-model) and mixed subs' unproven remainder. It is the caller-window base, not SP.
_Avoid_: hike_stack, stack argument

### VSA Classifications

**Range**: A bounded stack offset interval `[lo, hi]` where `lo` and `hi` are known integers.

**Typed Frame**: The emitted form where frame-proven accesses are typed GEPs into real storage — never address integers. It is THE stack model; there is no alternative path.

**Exception Lane**: The documented residual use of address integers (`inttoptr`) for accesses with no frame provenance — section and global constants. Everything frame-proven is typed.

**Convergence**: The requirement that the same C source lifted from its -O0 build and from its -O2 build, then optimized by the consumer, yields equivalent results of similar complexity. Sources whose -O2 build constant-folded the computation away are measured separately — that divergence belongs to the compiler, not the lifter.
**Infinite**: A widened stack offset interval `[lo, hi]` where one or both bounds represent unbounded growth.
**Unbounded**: A stack access whose address value set is completely unconstrained (`TOP`), spanning the whole stack frame.
**Dead**: A stack access on an unreachable execution path (`BOTTOM`), eliminated by DCE.
**VLA**: A stack access targeting a dynamic allocation frame.
