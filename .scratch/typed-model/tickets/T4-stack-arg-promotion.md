# T4 — stack-arg promotion + the SP convention (P1)

Spec: `.scratch/typed-model/spec.md` (binding constraints apply).
Design: `.scratch/o2-attribution/tickets/05-stack-arg-promotion.md`
(the measured baseline), **as settled by the 2026-09-10 grilling
session (this document is the authority where they differ)**.
Blocked-by: T3c (the single-predicate conformance).
Blocks: T5 (the convergence accounting order), the va_list re-model
lane.
Glossary: CONTEXT.md — Stack-Arg Promotion, SP Slot, Per-Invocation
Anchor, Resolved Call Site, Thunk, Caller-Window Parameter.

## The settled design (grilled 2026-09-10, owner's answers)

1. **Promotion (per-slot, total over resolved sites).** The callee's
   proven incoming stack slots become function parameters; the
   callers' outgoing stores become call arguments at every site whose
   target resolves. SysV fixes the correspondence (callee slots at
   `[entry_rsp + 8 + 8·i]`). Widths: the slot promotes at its stored
   width; narrower reads truncate the parameter; a wider read demotes
   the slot to memory. Unprovable slots stay on the window (mixed,
   per-slot — no per-sub all-or-nothing).
2. **The SP Slot (owner directive).** Every memory-touching sub gets
   an entry-block alloca holding its per-invocation anchor — the
   ptrtoint of its own frame (or region-alloca base for precise
   subs). Uniform rule; SROA erases the constant cases. NO sub takes
   an SP parameter: the `hike_stack` parameter and both T3 binding
   arms (precise SP-binds-to-param, constant anchor) are RETIRED.
3. **Per-invocation anchor.** `stack_0` = the SP Slot's value, bound
   at entry. SP-relative offsets are frame-relative; reentrancy-safe.
4. **Indirect calls resolve through the VSA (owner directive).** The
   call target's denotation (the `is_stack_access` predicate family
   on the target exp) classifies the site:
   - singleton lifted sub → a DIRECT call through its promoted
     signature (a Resolved Call Site);
   - bounded multi-target set, any foreign address, or unresolvable →
     the POINTER call, landing in the Thunk (or the target's existing
     memory convention);
   - Target-authoritative: the callee's promoted signature is the one
     true type; a site storing fewer slots passes undef for the rest
     (reading an unpassed arg is UB in the binary too); extra stores
     remain in the caller's frame memory.
5. **Thunks (internal, owner directive).** Every address-taken
   promoted sub emits a memory-convention twin (unpacks window memory
   → calls the promoted body), emitted with INTERNAL linkage — the
   consumer's optimizer sees through it (inlines it into callers,
   devirtualizes provable pointers), so the twin costs nothing where
   the site resolves anyway. Function-pointer data renders to the
   twin's address, so unresolvable sites stay sound. No target ever
   demotes.
6. **Caller-Window Parameter (the honest residual).** The window-base
   parameter survives ONLY for: variadic subs (the bridge) and mixed
   subs' unproven remainder. Renamed from `hike_stack` — it is the
   caller-window base, not SP. `check_allocas.sh`'s sp-roots
   modernize in the same commit (the SP Slot becomes a root;
   `hike_stack` leaves the grammar).
7. **va_list re-model = the follow-up lane** (NOT this ticket): the
   bridge above ships first; the re-model (LLVM-variadic tail /
   alloca'd overflow array) is the lane that retires the window
   parameter for variadic subs.
8. **Retaddr modernization.** The return-address slot's Caller tag
   dies with the real LLVM ret and must not force window parameters.

## Tests for indirect calls (owner directive)

New corpus sources (`src/progs/synth/`, PIE -O0 + -O2 lanes, stdout
checkable by the semantic harness):

- `fn_table_disp` — a handler table dispatch: `handlers[opcode](a,b)`
  with ≥3 handlers taking STACK args at -O0 (force >6 integer args'
  worth or big struct padding so outgoing stores exist) — the
  multi-target resolved-set class, promotion, and the thunk all at
  once.
- `jump_table_sw` — a switch with many cases compiled to a jump table
  (-O2 builds it), each case calling a distinct handler: the
  multi-target class through .rodata code addresses (interacts with
  T6's data-pointer rendering).
- `fn_single` — an indirect call the VSA resolves to a SINGLETON
  (the pointer provably one target): the direct-promoted-call path.
- `fn_escape` — an address-taken sub whose pointer escapes through
  memory to a site the VSA cannot resolve: the thunk path end-to-end.

Corpus growth (33 → 37) re-baselines every count — deliberate, the
sp_reload precedent; the battery's canaries are unaffected.

Unit pins (test_cbat, Test_seam fixtures): the target-resolution
predicate's four classes — singleton lifted sub (direct), bounded
multi-target (pointer call), foreign address (pointer call),
unresolvable/TOP (pointer call) — each pinned at the tag/emission
contract level, plus a thunk-shape pin (the twin's signature = the
legacy memory convention).

## The retirement inventory (from T3c's blocked-by-T4 section)

Everything T3c records as blocked by the parameter convention lands
here: the caller-window materialization lane, the Mixed two-base
select (dies except where the va_arg bridge genuinely needs it —
re-attributed in the verdict), the precise SP-binds-to-param arm, the
constant-anchor arm, the `sp_restores` edge-keyed mechanism as it
intersects the SP Slot.

## Battery protocol (you hold the shared plugin slot in your wave)

`eval $(opam env)` first; after every install `bash
src/record_provenance.sh`; battery artifacts on home disk
(`/home/tovpr/tm-battery/t4/`); never touch
`/home/tovpr/tm-battery/{merge-t1,merge-t3,t3,t3c}` or `/tmp/emit_*`.

Gates every iteration: `dune runtest` (failure set == the pre-existing
owner baseline; referee 0 mismatches), corpus emission rc=0 for BOTH
lanes (now 37 bins), strict -O0 semantics (all PASS), check_allocas
(modernized) green, strict opt-safety all PASS, -O2 pinned gate (the
failing set may only change by a PROVEN flip — golden + AGENTS.md move
in the merger's commit), both profiles build, instrumentation blocker
clean.

## Acceptance

- All gates green; NO sub carries an SP parameter (grep the emissions:
  no `hike_stack`; the caller_window parameter appears only in
  variadic/mixed subs' signatures).
- The four new indirect-call sources pass semantics at BOTH -O0 and
  -O2 lifts (strict, unless a -O2 failure is a recorded-class flip).
- **Convergence movement** (the prize — `scripts/semantic/
  convergence_report.sh` vs the pre-T4 reference): the memory-passed
  class (deep_chain, spill_many, many_args, alloca_vla, nested_calls,
  mixed_fp_int, union_overlap) collapses toward its o2+opt counts;
  every row before/after in the verdict.
- The promotion is a rule over proven pairs and resolved sites — no
  provenness gates, no per-site refusal; unresolved sites take the
  pointer/thunk path (the identity, not a stop).
- Verdict file: the design as landed, the retirement inventory's
  disposition (each item: died/bridged/re-attributed), the resolution
  classes' measured counts on the corpus (how many sites resolved
  singleton/multi/foreign/unresolvable), the gate table, the
  convergence table, the emission delta summary.

Worktree: `/home/tovpr/hike-t4`, branch `tm/t4-stack-args`.
