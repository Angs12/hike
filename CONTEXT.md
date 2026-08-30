# Hike

Hike lifts x86-64 ELF binaries to LLVM IR, splitting the flat stack into LLVM allocas via value-set analysis over BAP BIL.

## Language

### Stack model

**Stack Access**: A def whose right-hand side is a memory Load or Store whose address is derived from the Stack Pointer.
_Avoid_: direct_sp, stack reference, SP-relative def

**Relevance**: The exact set of defs and phis that transitively contribute a value to the address of a Stack Access.
_Avoid_: reachable, live, dependency closure, arg-setup

**Dynamic Allocation**: A definition that decrements the Stack Pointer by a non-literal size (VLA / alloca).
_Avoid_: VLA size def, runtime alloc, variable stack growth

**Stack Pointer (SP)**: The target-defined stack-pointer register (`Targetutils.sp`), the sole origin for Stack Access derivation.
_Avoid_: "RSP" string, RBP, frame pointer

### Analysis passes

**Relevance Analysis**: The forward-then-backward analysis that tags Stack Accesses and then their Relevance closure.
_Avoid_: restriction pass, taint, slice pass

**Trace-Partitioning (single-pass)**: Making a block's entry abstract state aware of the branch condition on its incoming edge, so the analysis is branch-sensitive rather than branch-blind; realized as one coupled pass where the deep backward walk runs inline at every conditional GOTO.
_Avoid_: Phase B, post-pass, `edge_views_of` (deleted), `partitioned_states` (deleted), `edge_view` (deleted)

**Edge-Splitting**: At a conditional jump, computing two refined successor inputs (taken refined by the condition, fallthrough by its negation) and transferring each to its destination block.
_Avoid_: edge view, branch partition

**Inverse Denotation (Deep Walk)**: The backward derivation of a block's pre-state from a post-edge constraint, via producer subtraction (`cstr' = cstr ∩ post(v)`) and trace-exact cell meets; what `refine_edge` computes inline at each jump.
_Avoid_: inverse_denote_exp (the shallow production no-op), guard-meet-only

**TAG State**: A per-block abstract state already refined by its incoming edge conditions; in the single-pass design this is simply the block's IN-state in the VSA solution.
_Avoid_: partitioned state, per-edge view

**100% VSA Tagging Invariant**: Every definition carrying a `Stack Access` tag is guaranteed to have a corresponding `VSA Info` tag (`Range`, `Infinite`, `Unbounded`, `Dead`, or `VLA`). Untagged stack accesses are prohibited.

### VSA Classifications

**Range**: A bounded stack offset interval `[lo, hi]` where `lo` and `hi` are known integers.
**Infinite**: A widened stack offset interval `[lo, hi]` where one or both bounds represent unbounded growth.
**Unbounded**: A stack access whose address value set is completely unconstrained (`TOP`), spanning the whole stack frame.
**Dead**: A stack access on an unreachable execution path (`BOTTOM`), eliminated by DCE.
**VLA**: A stack access targeting a dynamic allocation frame.
