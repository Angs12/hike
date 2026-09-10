# T9 design notes — the va_list re-model map (pre-digest, 2026-09-10)

Read-only exploration on `typed-model-program` @ `2e8f5a2` (pre-T4),
against the reference emissions `/home/tovpr/tm-battery/merge-t3c/
emit-{o0,o2}/` and objdump of `/tmp/corpus` + `/tmp/corpus_o2`. The
three variadic sources live in `src/progs/synth/`; the only other
variadic-facing traffic is extern `printf` calls.

## 1. Per-source idiom inventory

**`variadic.c` — `sum_n(int count, ...)`**
- Idioms: `va_start(ap, count)` (gp_offset=8 → 1 named GPR; fp_offset=48 → 0 named XMM); 7× `va_arg(ap, int)` inside a RUNTIME loop (count-driven); `va_end` (no-op at -O0). No va_copy.
- Stack-arg slots at -O0: **2** (60@window+0, 70@+8). va_arg consumes 5 reg-save ints + 2 overflow ints.
- Binary shape (`sum_n`@0x1139): GP saves RSI..R9 at RBP−0xa8..−0x88; `test %al,%al` + 8× `movaps %xmmN` (XMM save, RBP−0x80..−0x10); the 4 va_start field stores; loop does the canonical expansion `cmp $0x2f,%eax; ja overflow-arm`.
- -O2 build: **loop folded** (count const-prop'd → `sum_nconstprop0`); straight-line walk = 5 reg-save reads (Range) + 2 constant-offset overflow reads (Caller). **PASSES -O2 today.**

**`va_arg_vacopy.c` — `two_pass(int count, ...)`**
- Idioms: `va_start` (same constants); **`va_copy(ap2, ap)` before pass 1** (3×8-byte struct copy in the binary); pass 1 = 6× `va_arg(ap,int)` runtime loop + `va_end(ap)`; pass 2 = 6× `va_arg(ap2,int)` second loop + `va_end(ap2)`.
- Stack slots at -O0: **1** (i+6); the 6th va_arg of EACH pass reads overflow — pass 2 re-reads the same cell via the copy.
- -O2 build: **`two_pass` is INLINED into `main`** (no symbol; the lifted sub is `two_passconstprop0`). **FAILS -O2 today**: stale 6th element (`1 2 3 4 5 1` vs native `1 2 3 4 5 6`).

**`va_arg_mixed.c` — `consume_mixed(int seed, ...)`**
- Idioms: `va_start`; 5 straight-line `va_arg`s at fixed types: int(GPR), double(**XMM**), char*(GPR), long(GPR), int(GPR); no loop, no copy.
- Stack slots at -O0: **ZERO** (4 GPR + 1 XMM varargs all fit in regs).
- Binary shape: 5 GP reg-save stores + AL-tested `movaps`×8; at -O2 **the whole va_arg walk folds away** (args read straight from reg homes), but the 4 va_start field stores and ONE `movaps xmm0` remain.
- **The only -O0 Dead-warn binary** (`hike: guarded: sub @consume_mixed: stack access classified Dead ... def RAX rhs=mem[RBP - 0x100, el]:u64`); each `movaps` lifts to an alignment-guard + i128 store + `@llvm.trap` arm — **9 trap arms in the -O0 lift, NOT binary ud2** (BAP's movaps semantics; `create_interrupt`, `src/bil2llvm_calls.ml:390-401`, reached via `Int` edges `src/bil2llvm.ml:90-100` and `@interrupt:` calls `bil2llvm_calls.ml:674-676`). **FAILS -O2 today (rc=132 SIGILL)** — and critically: its -O2 lift has **zero window traffic** (see §3).

## 2. Today's lift paths (file:line)

**Tag production** — `src/cbat_vsa/cbat_vsa.ml`: kind enum + class doc :404-421; `classify` :447 (denotation → Range/Infinite/Unbounded/Dead); the ONE predicate `is_stack_access` :496-509 (StackOff denotation or in-band degraded; **the reloaded-pointer channel is structural: spilled RSP-derived values are StackOff cells**); `extract` :511-589 (every def denoted; tag = `classify(relativize(denotation))`); overlap merge :591-616 (**Range-kind defs only** participate); the lane split `caller_split` applied at :617-622: entirely-above → `Caller`, entirely-below → Range/Infinite, two-sided/wrapped → **`Mixed`** (`src/convutils.ml:96-104` is the physical alias `vsa_kind`).

**Emitter dispatch** — `src/bil2llvm_mem.ml` `mem_access` :208-264: Range/Infinite → the uniform rule via `create_addr_ptr` (`src/bil2llvm_section.ml:138-157`; the license `frame_wrap_license` set per-def at `bil2llvm_mem.ml:281-284`); `Caller` → `caller_mem_access` :124-148 (`inttoptr(hike_stack + (word − stack_0))`, one base); **`Mixed` → `mixed_mem_access` :150-182 — the two-base select** (`base = select(word ≥ stack_0, hike_stack + off, word)`; emitted markers `%mixed_off/%is_caller_arg/%caller_addr/%arg_addr` :169-176; then `mem_access_at_ptr` :77-122 rewrites the mem node through the materialized pointer); Dead → warned poison :253-263. `stack_0` = `anchor_i64` for frame subs, the `hike_stack` param for precise subs.

**Window threading** — a sub takes the `hike_stack` parameter iff any def is Caller/Mixed (`src/bil2llvm.ml:520-533`, `has_positive`; `hike_stack_var` defined `src/convutils.ml:160-162`). At call sites `create_call_args` (`src/bil2llvm_calls.ml:41-72`) passes the caller's model SP at the call block; the window is VIRTUAL: caller stores 60/70 through Range-tagged frame GEPs into main's `%frame` (out_variadic.ll:38,43), the callee's caller-arm arithmetic `hike_stack + (word − stack_0)` lands on exactly those cells — chained anchor-linear integers across two different `%frame` allocas. Post-call SP restore: `restore_sp_after_call` :11-38.

**Frame geometry** — `src/hike_stack_model.ml`: Mixed sizes the frame's NEGATIVE extent only (:300-316, :348-352); `regions_of_sub` **excludes** Mixed from region splits (:141-153) — the va walk never joins a `stack_rN` region.

**Measured footprint today:** Mixed selects corpus-wide = 3 (-O0): variadic ×1 (out_variadic.ll:1281-1285, feeding `load i32` :1286), va_arg_vacopy ×2 (pass 1 :1786-1791, pass 2 :2096-2101). va_arg_mixed -O0 has **0** Mixed sites (no stack args). At -O2: variadic routes 2 constant Caller reads (:183-193, passes); vacopy routes **no Mixed at all** — one constant Caller read (:1158-1160) plus an **untagged raw `inttoptr` of a reloaded-pointer loop phi** (:1357) — and fails; va_arg_mixed's -O2 lift is PRECISE (29 `stack_rN` allocas, **no `%hike_stack` param at all**) and fails by SIGILL.

## 3. The va_list object's storage facts

The 24-byte `__va_list_tag {u32 gp_offset; u32 fp_offset; void *overflow_arg_area; void *reg_save_area}` is a LOCAL of the variadic callee (`va_list ap` = the struct array) — **in the callee's own frame**, alongside the reg-save area (48 B GP + 128 B XMM). The overflow area is the caller's outgoing-arg window (SysV: `rbp+16` = `stack_0+8`). In the lifted world:
- Struct fields, reg-save cells, named-arg spill slots: Range-tagged own-frame cells → frame GEPs (sound; va_start's stores e.g. out_variadic.ll:969/:974, vacopy :1261/:1266).
- `va_copy` = three 8-byte own-frame loads/stores (struct→struct; both cells Range) — **sound at -O0 today**.
- The walk pointer (`reg_save_base + gp_offset` vs the overflow word) is a RUNTIME value crossing the entry-RSP boundary → the Mixed class at -O0.
- **The recorded -O2 vacopy residual** (T3 verdict §re-attribution, confirmed in IR): the -O2 emission has no Mixed select; the failing pass-2 reads route through the Caller lane and the **untagged raw-inttoptr lane over a reloaded-pointer phi** (`%1008 = phi … ; inttoptr %1008; load` — emit-o2/out_va_arg_vacopy.ll:1316-1357) — the va_list state round-trip (register-cached counters + spilled/reloaded pointers after gcc inlined `two_pass` into `main`). The residual is NOT address-materialization arithmetic; whether the window re-model dissolves it is precisely what "re-attribute under the new model first" must measure.
- **va_arg_mixed's -O2 SIGILL is NOT window traffic**: its -O2 lift has no Caller/Mixed/inttoptr sites and no hike_stack param. It is the L1 class (Dead-poison/alignment-guard over the region-split shape). T9's acceptance expectation that va_arg_mixed flips green **cannot come from the re-model alone** — re-attribution first, exactly as the ticket says.

## 4. The two T9 options' transformation surfaces

**(a) The alloca'd overflow array**
1. Surface: subs with Caller/Mixed tags (today's `has_positive` test is the class predicate). One entry-block alloca sized by the ABOVE-entry extent of the tags (the symmetric twin of `frame_dims`' negative fold, hike_stack_model.ml:308-352 — call it window_dims); SysV correspondence: window offset w ↔ array index w−8.
2. Populate: T4's promoted overflow parameters stored at entry in SysV order; unresolved (pointer) sites go through T4's Thunk, which unpacks window memory → array. The reg-save side needs NO array: the register varargs are already the callee's own lifted parameters (RSI..R9/YMM0-7), spilled by the binary's own prologue into own-frame cells.
3. Emission rule change: the Mixed select's above-arm (`bil2llvm_mem.ml:173-176`) becomes `gep overflow_array, (off − 8)` instead of `hike_stack + off` + inttoptr; same for the Caller lane (:129-148) — the -O2 constant reads become typed GEPs. Below-arm unchanged.
4. Window death: `has_positive` stops forcing the parameter for variadic subs; `create_call_args`' threading and the is_main exception shrink with T4's modernization.
5. The binary's own va_start/va_arg/va_copy arithmetic is untouched — gp_offset/fp_offset are set by the binary's stores, so **no named-arg-count fact is needed**, and the walk order stays in the lifted code.

Soundness corners (a): (i) **reg-save vs overflow walk order** — safe by construction (the array serves only the above side; the gp_offset<48 boundary stays in the binary's own arithmetic); (ii) **array completeness** — the size rule must cover the tags' above-extent, including T4's unproven slots (undef-passed at resolved-but-partial sites per T4's design — poison-adjacent, note it); (iii) **va_list ESCAPE (vprintf forwarding)** — a forwarded va_list carries the overflow word; a receiver's untagged raw inttoptr needs that word to be a REAL address. Either redirect at the va_start store (store `ptrtoint(array)+8` so the field holds a real pointer) or flag the escape class — absent from the corpus today, it is the residual that could keep a window-ish fact alive; (iv) `check_allocas.sh` needs the new storage shape asserted.

**(b) The LLVM-variadic tail**
1. Surface: re-declare the lifted variadic sub LLVM-variadic (named prefix = the binary's named args — a NEW producer fact read off the va_start store constants); promoted overflow params pass as varargs; resolved direct sites emit variadic calls (AL=#XMM must now be computed — today extern variadic calls unconditionally over-pass 8 doubles, harmless for externs, load-bearing for lifted variadic callees); `llvm.va_start` replaces the binary's 4 field stores; the lifted walk is REWRITTEN to the LLVM `va_arg` instruction (result type from the load width); va_copy → memcpy of the LLVM va_list (x86-64 va_list is psABI-trivially-copyable); variadic thunks for pointer sites.
2. Soundness corners (b): the rewrite is sound **only where the lifted walk maps 1:1 onto LLVM's lowering** (the ticket's own caveat) — recognizing "pure va_arg idiom" through loop phis (variadic's runtime loop) and across register-cached counters is a per-shape recognition with refusal pressure (gate-shaped, in tension with the no-gates doctrine); **the inlined class is fatal**: the -O2 vacopy's walk lives inside `main`, which cannot be declared variadic — option (b) has NO rule for the exact residual T9 targets; odd-width va_arg types (default argument promotions) need complete rules for totality.

**Asymmetry that decides the design:** (a) is sound for the DYNAMIC walk by LAYOUT (a dynamic GEP into the SysV-ordered array needs no per-slot proof), serves the -O2 straight-line Caller reads and the inlined class, and composes with T4's promotion/thunk. (b) covers only walks inside subs the lift can declare variadic and needs a 1:1 recognition proof.

## 5. The unproven remainder verdict

- After T4's promotion, constant-offset incoming stack reads (the -O2 variadic shape) have **proven** slot correspondence — absorbed by promotion +(a)/(b).
- The **dynamic loop-carried walk (the -O0 Mixed class) has NO per-slot proven correspondence**: the VSA tag is a two-sided hull; the slot index exists only in the walk's arithmetic. This is the class that would force caller_window to survive IF the re-model had to prove slots. Option (a) does not need the proof — the layout IS the correspondence — so **under (a) the window parameter can die for the whole variadic class**; the flagged survivors are the va_list-escape class, UB reads past the passed args, and T4's own mixed (non-variadic) unproven remainder, which is a separate residual.
- va_arg_mixed must be de-scoped from "expected flip via the re-model": its failing -O2 lift carries no window traffic at all; the flip, if it happens under T9's battery, comes from the L1 poison/alignment-guard lane and should be attributed as such, not credited to the re-model.
