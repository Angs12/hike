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

**100% VSA Tagging Invariant**: Every definition carrying a `Stack Access` tag is guaranteed to have a corresponding `VSA Info` tag (`Range`, `Infinite`, `Unbounded`, `Dead`, or `VLA`). Untagged stack accesses are prohibited.

### VSA Classifications

**Range**: A bounded stack offset interval `[lo, hi]` where `lo` and `hi` are known integers.
**Infinite**: A widened stack offset interval `[lo, hi]` where one or both bounds represent unbounded growth.
**Unbounded**: A stack access whose address value set is completely unconstrained (`TOP`), spanning the whole stack frame.
**Dead**: A stack access on an unreachable execution path (`BOTTOM`), eliminated by DCE.
**VLA**: A stack access targeting a dynamic allocation frame.
