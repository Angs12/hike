# Research note — prior art + optimizer facts for the settled call/SP/thunk/varargs design (2026-09-10)

Web research; every claim sourced. Preserved as the program's research
record; the actionable items are forwarded to T4's lane.

## Q1. Prior art — stack pointer, stack args, indirect calls

**mctoll (microsoft/llvm-mctoll).** The repo was renamed/restructured;
the old `Microsoft/MSR-MCT` URL is dead (API 404; no Wayback snapshots)
— verified against live `master` and a 2022 thesis.

- **SP as a function argument: NOT CONFIRMED — the live source
  contradicts it.** Raised functions take arguments only from the
  C-ABI argument registers (`buildFuncArgTypeVector` builds from
  GP/SSE argument registers; `getRegOrArgValue` maps a physical
  register to a function argument only when it IS an argument
  register — RSP is not one): [X86FuncPrototypeDiscovery.cpp](https://github.com/microsoft/llvm-mctoll/blob/master/X86/X86FuncPrototypeDiscovery.cpp),
  [X86MachineInstructionRaiserUtils.cpp `getRegOrArgValue` L2256–2290](https://github.com/microsoft/llvm-mctoll/blob/master/X86/X86MachineInstructionRaiserUtils.cpp).
  The "mctoll passes the stack pointer" claim is FOLKLORE.
- **Per-sub allocas, yes — aggressively.** Stack references are
  rewritten to per-function `alloca` stack slots (`getStackAllocatedValue`;
  RSP's SSA value binds to the alloca) —
  [X86MachineInstructionRaiserUtils.cpp L1254+](https://github.com/microsoft/llvm-mctoll/blob/master/X86/X86MachineInstructionRaiserUtils.cpp),
  [X86MachineInstructionRaiser.cpp L4039–4042](https://github.com/microsoft/llvm-mctoll/blob/master/X86/X86MachineInstructionRaiser.cpp).
  It even uses allocas as phi-substitutes for multi-pred register
  values and relies on LLVM `opt` to "convert these stack accesses to
  phi nodes" — [Fink thesis §2.5.3](https://finkmartin.com/papers/bsc_fink.pdf).
- **Stack-passed args: NOT promoted — silently dropped.** "For every
  argument, MCTOLL looks up the reaching value for the appropriate
  argument register. If there is no reaching value, it assumes the
  argument has been optimized and passes a constant 64 bit integer of
  zero" ([X86MachineInstructionRaiser.cpp call construction L5285–5348](https://github.com/microsoft/llvm-mctoll/blob/master/X86/X86MachineInstructionRaiser.cpp);
  [thesis §2.5.2](https://finkmartin.com/papers/bsc_fink.pdf)).
- **Indirect calls:** no target resolution; calls constructed only to
  symbol-table functions.

**remill / McSema (Trail of Bits).** Every lifted function has exactly
three arguments: State pointer, PC, Memory pointer
([ABI.h](https://github.com/lifting-bits/remill/blob/master/include/remill/BC/ABI.h));
the SP is an ordinary field in the one State struct; NO per-sub frames;
program memory is one flat `Memory*` threaded through everything
([DESIGN.md](https://github.com/lifting-bits/remill/blob/master/docs/DESIGN.md),
[INTRINSICS.md](https://github.com/lifting-bits/remill/blob/master/docs/INTRINSICS.md)).
Calls — including INDIRECT — are never typed LLVM calls: everything
goes through `__remill_function_call(State&, addr_t, Memory*)`-style
intrinsics ([Intrinsics.h L112–126](https://github.com/lifting-bits/remill/blob/master/include/remill/Arch/Runtime/Intrinsics.h)).
The typed-signature program in that family is **anvill** (bitcode "in
the form Clang would produce") — no varargs/SP parameters in its
schema ([Specification.h](https://github.com/lifting-bits/anvill/blob/master/include/anvill/Specification.h)).

**retdec.** Registers — including SP — are GLOBAL variables; every
control transfer is a pseudo-intrinsic taking the integer target
(`@__pseudo_call(i32)`) ([Capstone2LlvmIr wiki](https://github.com/avast/retdec/wiki/Capstone2LlvmIr)).

**Implications.** hike's settled design (per-sub typed frames; SP never
a parameter but a private slot; stack args PROMOTED to real call
parameters; VSA-resolved singleton indirect calls as direct calls) is
**more aggressive than all four prior arts** — none promotes stack
args; only mctoll approaches per-sub allocas (untyped spill slots,
punting SSA-ization to opt). Confirmation the design is ahead of
standard practice: no prior-art guarantee exists; the battery is the
only oracle. Prior art WARNS about exactly what hike already knows:
remill/retdec route every unresolved indirect target through
intrinsics because resolving targets at lift time is hard — the
internal-linkage thunk is the same total-coverage move in LLVM-native
vocabulary.

## Q2. LLVM optimizer facts (opt-21 era)

**(a) Devirtualization of an `internal` function called through a
pointer, without PGO: YES**, in the module pipeline:
- **IPSCCP with function specialization** runs at O2
  (`IPSCCPPass(AllowFuncSpec=...)`), followed by
  `CalledValuePropagationPass` ("Attach metadata to indirect call sites
  indicating the set of functions they may target"), then
  `GlobalOptPass` — [PassBuilderPipelines.cpp release/21.x ~L1168–1180](https://github.com/llvm/llvm-project/blob/release/21.x/llvm/lib/Passes/PassBuilderPipelines.cpp).
  Pipeline comment: "Propagate constants at call sites into the
  functions they call. This opens opportunities for globalopt (and
  inlining) by substituting function pointers ... with direct uses of
  functions".
- The promotion: `SCCPSolver::tryToReplaceWithConstant` — the callee
  operand resolving to a single `Function` constant rewrites the
  indirect call DIRECT ([SCCPSolver.cpp L69+](https://github.com/llvm/llvm-project/blob/release/21.x/llvm/lib/Transforms/Utils/SCCPSolver.cpp));
  FunctionSpecializer clones callers around constant function-pointer
  arguments ([SCCP.cpp L46–48, L161–164](https://github.com/llvm/llvm-project/blob/release/21.x/llvm/lib/Transforms/IPO/SCCP.cpp)).
  Then the ordinary CGSCC inliner handles it. WholeProgramDevirt is
  LTO-only — irrelevant per-module.

**(b) Does `internal` linkage matter?** For inlining a promoted direct
call: no (having the definition in-module suffices). Where `internal`
pays: STB_LOCAL means nothing outside the module observes the address,
so IPSCCP/GlobalOpt treat address-taken-ness as module-local and
GlobalDCE deletes the thunk after full devirt
([LangRef linkage](https://llvm.org/docs/LangRef.html#linkage-types),
[Passes.html internalize](https://llvm.org/docs/Passes.html)). hike's
all-hike-owned bodies start with that for free.

**(c) SROA/mem2reg on an entry-block scalar alloca stored once:**
promoted to SSA **iff every use is a plain load/store**
([Passes.html mem2reg/sroa](https://llvm.org/docs/Passes.html)). If the
address escapes (passed to a call, stored into another alloca), it
stays memory — sound, not register-resident.

**Implications.** The internal-linkage thunk is well-positioned: a
singleton pointer value set → IPSCCP devirt + inline with no hike help;
otherwise a legit indirect call — sound either way. **Battery check:
thunks must not accidentally escape their address.** The SP Slot
promotes at zero cost **only if the slot's address never escapes** —
the variadic caller-window bridge must pass the window base VALUE,
never the SP slot's address.

## Q3. va_list lowering facts and re-modeling precedent

**psABI:** `va_list = struct {u32 gp_offset; u32 fp_offset; void
*overflow_arg_area; void *reg_save_area} [1]`; `overflow_arg_area` =
the address of the first stack-passed argument IN THE CALLER'S
OUTGOING AREA; the walk checks `gp_offset > 48 − num_gp*8` /
`fp_offset > 176 − num_fp*16` then fetches reg-save or aligns/advances
the overflow pointer ([x86-64 psABI §3.5.7](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/master/x86-64-ABI/low-level-sys-info.tex)).

**Who lowers va_arg:** Clang's frontend, inline psABI steps
([clang Targets/X86.cpp EmitVAArg L3214+](https://github.com/llvm/llvm-project/blob/release/21.x/clang/lib/CodeGen/Targets/X86.cpp))
— "the code generator does not yet fully support va_arg on many
targets" (LangRef). `@llvm.va_start` on x86-64 lowers to field stores
plus frame indices for `overflow_arg_area`/`reg_save_area` — objects in
the CALLEE's machine frame ([X86ISelLowering.cpp LowerVASTART L26718+](https://github.com/llvm/llvm-project/blob/release/21.x/llvm/lib/Target/X86/X86ISelLowering.cpp)).

**Lifter precedent for re-modeling a variadic callee as
LLVM-variadic: essentially NONE** — remill/anvill never model variadic
callees; mctoll is caller-side only; retdec's lift keeps registers as
globals. **The known soundness trap validates T9's choice:** LLVM's
real `va_start` binds `overflow_arg_area` to the callee's incoming
stack-arg frame object — which DOES NOT EXIST under promoted
parameters (no shared stack window). The binary's own reg-save spill
pattern would also diverge from LLVM's `RegSaveFrameIndex`. The
alloca'd overflow array is the only variant whose `va_copy`/aliasing
story is plain memory (SysV `va_list[1]` copies are struct copies;
[stdarg(3)](https://man7.org/linux/man-pages/man3/va_copy.3.html)).

**Implications.** Bridge-then-replace is the right ordering; the
caller-window base parameter is the only sound stand-in for
`overflow_arg_area` until the array lands. Battery checks: (1) a lifted
variadic callee's window reads still hit the caller's window when the
caller used promoted stack params — the exact spot where "promoted
params + no shared stack" can silently diverge from the binary's
overflow arithmetic; (2) the va_arg_* corpus binaries that pass va_list
to `v*printf` natives are the canary — a re-modeled LLVM-variadic
callee would hand natives hike-internal pointers instead of psABI-shaped
ones.
