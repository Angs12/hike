# T4 — verdict: stack-arg promotion + the SP convention

Landed 2026-09-10 on `tm/t4-stack-args` (worktree `/home/tovpr/hike-t4`),
branched at the T3c tip `2e8f5a2`. Final provenance: `bundle=76cb1c1b0ce17d16`
(re-run after the last install; `src` sha16 in the provenance file). Battery
artifacts: `/home/tovpr/tm-battery/t4/` (own corpus lanes `corpus`,
`corpus-o2`; emissions `emit-o0`, `emit-o2`; semantics `sem-o0`, `sem-o2`,
`semopt-o0`; census `census.txt`; convergence `conv.log`).

Corpus grew 33 → 37 (the four new indirect-call sources) — deliberate, the
sp_reload precedent; the battery canaries are unaffected.

## The design as landed (each of the seven points — what exists where)

1. **Promotion (per-slot, total over resolved sites).**
   Producer: `callee_side` (`src/hike_vsa.ml`) classifies every
   Caller-tagged def from its tag + rhs shape: a LOAD at the singleton
   offset k = 8+8i within the cell promotes to slot i (`prom_slots`,
   `prom_arity` = max index + 1). Emitter: `compute_sub_sig`
   (`src/bil2llvm.ml`) appends positional `hike_slotN` parameters
   (width 64 — the SysV slot width) after the register lanes;
   narrower reads truncate (the existing def-width coercion), a wider
   read demotes the slot (the `callee_side` window arm), unread slot
   positions below the max still take params (positional alignment).
   Sites: `caller_side` maps each call block's outgoing stores to slot
   indices by the SysV-fixed correspondence k = a − d (a = the store's
   relative offset, d = the SP's offset at the call — both singleton
   denotations; `prom_sites`), and `create_call_args` passes the
   stored value (`fr.outgoing`); a site storing fewer slots passes
   undef. Unprovable slots stay on the window (per-slot mixing — a
   sub with both promoted slots and window traffic carries both).

2. **The SP Slot.** `create_sub` builds, for every storage-carrying
   sub, `%sp_slot = alloca i64`, stores the per-invocation anchor
   (the ptrtoint of the sub's own frame — or of its first region
   alloca for precise subs), and `build_entry_block` binds the SP
   local to the slot's load (`stack_0`). NO sub takes an SP parameter:
   `hike_stack` is deleted from the grammar (grep: zero occurrences in
   `src/`, zero in the emissions); both T3 binding arms (precise
   SP-binds-to-param, the entry sub's `llvm.stacksave`) are deleted.
   SROA erases the store-load pair (verified: opt-21 handles the form;
   opt-safety below).

3. **Per-invocation anchor.** `stack_0` = the SP Slot's value, bound at
   entry. The window lanes (`caller_mem_access`/`mixed_mem_access`)
   subtract it (the differences cancel, exact offsets); the
   uniform materialization lane computes frame-relative GEPs from it.
   Reentrancy-safe (private per invocation).

4. **Indirect calls resolve through the VSA.** `resolve_target`
   (exported on `Hike.Vsa`): the target exp's denotation is a
   singleton whose word names a lifted sub (the symtab + the program's
   name map) → `Some tid`; a bounded multi-target set, a foreign
   singleton, and TOP → `None` (each of the three None arms IS the
   pointer-call identity — no refusal without an emission rule:
   multi/foreign/unresolvable are the three classes the pointer call
   serves). `create_indirect_call` dispatches on `prom_resolved`
   (keyed by jmp tid): `Some t` → the direct call through t's promoted
   signature (a Resolved Call Site); `None` → the pointer call through
   the synthetic indirect signature. Target-authoritative signatures:
   sites storing fewer slots pass undef; extra stores remain in the
   caller's frame memory (see the storage closure below — they are
   REQUIRED to remain).

5. **Thunks.** `create_thunk` (`src/bil2llvm_calls.ml`): every promoted
   sub (arity > 0, `@main` excepted — its signature branch is fixed)
   emits a memory-convention twin at `@<sub>_hike_thunk`, INTERNAL
   linkage. Its signature = the synthetic indirect convention (every
   convention register lane — integer and vector — plus the
   caller-window base), so a pointer call's argument layout matches
   the twin's parameter layout position for position (the window base
   lands in the same stack slot). The twin unpacks the window slots
   ([window + 8 + 8i]) and forwards the register lanes + slots to the
   promoted body. Function-pointer data renders to the twin: the
   initializers render inside `emit_program` through the ONE address
   map (`lookup_native_fn` consults the thunk registry) — see the
   one-context fix below. No target ever demotes.

6. **Caller-Window Parameter.** `hike_window` (renamed from
   `hike_stack`): appended last in a sub's signature iff the producer's
   window-traffic classification demands it (`prom_window`). The rule
   that computes it — every input a denotation-derived fact: (a) a
   Caller span lo ≠ hi (an unproven slot set); (b) a Mixed tag
   (two-sided/wrapped — the two-base rule); (c) a Caller STORE (a
   write into real caller memory); (d) a Caller load wider than the
   cell (a wider read demotes the slot). The retaddr cell's Caller(0,0)
   LOAD does NOT force the window (point 8); a k=0 store does (it
   writes real caller memory). Consumers: variadic subs' va_arg
   overflow reads (the bridge until T9) and mixed subs' unproven
   remainder; the pointer-call path passes it to thunks.
   `check_allocas.sh` modernized in the same commit: the sp-roots are
   the SP Slot load, the anchor ptrtoint, and `%hike_window`;
   `%hike_stack` left the grammar.

7. **va_list re-model** — NOT this ticket (T9); the bridge above is its
   predecessor. Measured: `variadic`, `va_arg_mixed`, `va_arg_vacopy`
   pass -O0 strict under the bridge.

8. **Retaddr modernization.** Caller(0,0) loads (the return-address
   cell) bind `undef` (`mem_access`'s retaddr arm); they die with the
   real LLVM ret (DCE sweeps them) and never force a window parameter.

## The retirement inventory (T3c's BLOCKED-BY-T4 — each item's disposition)

| item | disposition |
|---|---|
| the SP anchor (caller-threaded `hike_stack` / the `llvm.stacksave` bridge) | **DIED** — the SP Slot; both T3 binding arms deleted; `hike_stack` zero in src/ and emissions |
| the 21 T3c re-framed subs | **RECOVERED** — measured per sub below (all 21 re-converted to regions; the ranged regions convert because the recovery rule serves them) |
| the servability clause in `regions_of_sub` | **DIED, replaced by the lattice rule** (see doctrine): `regions_of_sub` is purely geometric + the write-closed join; the SP-lane-vs-region closure moved to the producer's escape walk (`sp_extents`) — an escape joins the sub to Frame |
| the caller-window materialization lane (`caller_mem_access`) | **RE-ATTRIBUTED** — kept for the variadic bridge + mixed remainder + thunks, now over `hike_window` (the caller's SP at the call), stack_0 = the private anchor |
| the Mixed two-base select | **RE-ATTRIBUTED** — kept for the window-residual class (variadic); inventoried in T9's scope |
| `sp_restores` (the edge-keyed post-call SP mechanism) | **KEPT (re-attributed)** — the SP Slot anchors the ENTRY value only; the restore still un-pushes after calls (load-bearing for the outgoing-store addresses) |
| `prove_nonneg`'s store-chain seed | **NOT RE-ATTEMPTED** — the T4 model change did not dissolve the T3c failure (the L-D2/L-D6 pins still fail on the pristine-tip baseline); per the ticket, measured, never forced |
| the region-GEP lane (T3c: "decorative") | **IS the access path** — precise subs' singleton cells emit region GEPs (e.g. many_args `sum12`: 7 regions; spill_many `hammer`: 31) |

## The 21 subs' region-precision recovery (measured per sub, -O0 emissions)

deep_chain@f10 7, deep_recursion@fib 4, factorial@factorial 11 + @inc 7,
fizzbuzz@fizzBuzz 4, fizzbuzz_safe@fizzBuzz 6, fptr_table@fn0-3 20/15/10/5,
landmark_loop_1000@main 3, list@main 1, many_args@sum12 7,
mixed_fp_int@main 4, nested_calls@level5 6, nested_struct@sum_fields 16,
setjmp_longjmp@deep_nested 8, spill_many@hammer 31,
struct_arr_dynidx@runtime_idx 9, tail_callish@d 5, union_overlap@member_for 2
— **all 21 back at their T3c-baseline region counts.** Frame-model by
construction (not loss): sret_big@main (its `&a` escapes — the closure),
va_arg_mixed/va_arg_vacopy/variadic (the window bridge), and sret_big
build/checksum stay Frame? — build/checksum remain precise (17/5 regions);
their copy-out class is the inventory below.

## The resolution-class census (-O0 emissions, 37 bins)

- promoted signatures (`hike_slotN` params): **8 modules**; thunks
  emitted: **12** (`define internal ... _hike_thunk`).
- site maps with mapped slots: **64** call blocks (probe census, all
  subs); per-module slot counts match the SysV layout (e.g. many_args
  main: slots 0-5; fn_escape main: slots 0,1).
- resolved-singleton sites (direct promoted calls): **2** in
  fn_single (`call { i64, i64 } @add3(...)` — the class end-to-end),
  plus every DIRECT call to a promoted sub (the corpus's many_args,
  factorial, ... calls all direct).
- pointer-call sites (multi/foreign/unresolvable): **6** corpus-wide —
  fn_table_disp (the multi-target dispatch), fn_escape (the unresolvable
  argc-indexed escape), fptr_table (the pre-existing class), and 3 more.
- jump_table_sw: the dispatch is an indirect JUMP (not a call) — its
  handlers are direct calls; the source exercises the -O2 jump-table
  shape + T6's data-pointer rendering.
- window-param subs: **41** (probe census; variadic/mixed + thunks).

## Doctrine section (the case-count delta; the owner's bar)

Deleted by this lane: the `hike_stack` parameter and its threading arms
(`create_call_args`' precise/frame dance), the `llvm.stacksave` bridge,
the T3c servability clause (`unservable_stack_traffic`, ~40 LOC), the
`~sol` parameter of `regions_of_sub`, the tags-empty/tags-present fork in
`frame_dims` (folded into one extent fold), `site_provable` (a boolean
shadow of the structured `site_slots` — deleted before landing per the
owner's audit), hike.ml's pass-2 initializer loop (moved inside
`emit_program`, deleting the second ctx), and the mem-fission guard arms
that had duplicated the fallthroughs. Added: ONE new predicate family
(`resolve_target` — the four-class target classification in ONE
structure), ONE closure rule (an escape joins Frame), ONE write-closed
join (site stores keep Frame storage), and the twin (one function built
by one rule). The dispatch arms in `mem_access` grew by the promoted-slot
read and the retaddr arm — both complete rules over record facts, no
"cannot happen" arms. The one remaining shape assert (the promoted
parameter's binding) is justified by construction: arity = max index + 1 →
the sig carries the slot → the arg joins the transfer set via arg_set →
add_args_to_vars + the phi plumbing bind it in every block; the arm joins
the existing `get_phi` shape-assert idiom.

## Addendum items (the three battery checks)

1. **Window base is a VALUE, never the slot address**: grep over all 37
   -O0 emissions — `ptr %sp_slot` appears ONLY in alloca/store/load
   (the entry trio); **0 call arguments reference the slot's address**
   (the window/callee arg is the caller's SP SSA value, the slot's
   LOADED content). The address-escape that would pin the slot to
   memory does not exist.
2. **Variadic bridge**: `variadic`, `va_arg_mixed`, `va_arg_vacopy`
   pass -O0 strict (the va_arg overflow reads hit the CALLER's window
   cells — the caller's outgoing stores are required to stay memory by
   the site-store write-closed join, so the bridge arithmetic and the
   promoted world agree).
3. **Thunk address-escape**: no thunk stores its own address; the only
   thunk-address data is the intended fn-pointer rendering
   (`ptrtoint @..._hike_thunk` in fn_single/fn_table_disp's volatile
   cells — module-local values, what IPSCCP/GlobalOpt devirtualize
   through). Internal linkage confirmed.

## Gate table (the final tree)

| gate | result |
|---|---|
| build, default + vsa-debug profiles | rc=0 ✅ |
| instrumentation blocker (exercised by both builds) | clean (rc=0) ✅ |
| referee (`clpequiv`) | **2,861,148 checks / 0 mismatches** ✅ |
| `dune runtest` | 516 ok; failure set == EXACTLY the 8 pre-existing (E2eD-7/8, LM F1-*) ✅ |
| new unit pins | T4-RES ×4 (the resolution classes), T4-PROM ×2, T4-THUNK ×5, T4-PTR ×3 — all PASS ✅ |
| -O0 emission | 37/37 rc=0 ✅ |
| -O0 structural asserts (check_allocas, modernized) | 185 passed / 0 failed ✅ |
| -O0 strict semantics | **33 PASS / 4 FAIL** — the struct-copy class, inventoried below ⚠️ |
| -O0 strict opt-safety | 32 PASS / 5 FAIL (the 4 + array_local under opt) ⚠️ |
| -O2 emission | 37/37 rc=0 ✅ |
| -O2 structural asserts | 180 passed / 0 failed ✅ |
| -O2 pinned semantics | **29 PASS / 8 FAIL — PIN MOVED**: REGRESSION fizzbuzz_safe, spill_many; IMPROVEMENT va_arg_vacopy (golden); + fn_table_disp, jump_table_sw (new sources, first -O2 measurement) ⚠️ |
| provenance | bundle `76cb1c1b0ce17d16` (final tree) ✅ |

## Convergence (vs the pre-T4 reference `/home/tovpr/tm-battery/merge-t3c/conv.log`)

| source | pre (o0,o2,i0/i2) | post | movement |
|---|---|---|---|
| many_args | SAME/SAME 121/4 | SAME/SAME **58/4** | the promotion prize: o0+opt halved ✅ |
| mixed_fp_int | SAME/SAME 136/4 | SAME/SAME **68/4** | halved ✅ |
| alloca_vla | SAME/SAME 65/4 | SAME/SAME 65/4 | unchanged |
| variadic | SAME/SAME 185/77 | SAME/SAME 185/**27** | o2 side collapsed ✅ |
| sret_big | SAME/SAME 172/228 | DIFF/SAME **140**/228 | o0 improved, raw strict red (inventory) |
| struct_by_value | SAME/SAME 169/4 | DIFF/SAME **139**/4 | same class |
| nested_struct | SAME/SAME 129/4 | DIFF/SAME **90**/4 | same class |
| deep_chain | SAME/SAME 323/4 | SAME/SAME 323/4 | unchanged — its args are register-passed; no stack slots exist to promote |
| nested_calls | SAME/SAME 75/4 | SAME/SAME 75/4 | unchanged (register-passed) |
| spill_many | SAME/SAME 134/4 | SAME/**DIFF** 134/4 | o2 REGRESSION (inventory) |
| fizzbuzz_safe | SAME/SAME 87/250 | SAME/**DIFF** 101/40 | o2 REGRESSION (inventory) |
| union_overlap, byte_copy, va_arg_mixed, va_arg_vacopy | the golden DIFFs | unchanged/IMPROVED | va_arg_vacopy o2 flip candidate |

The promotion prize landed where stack slots exist (many_args, mixed_fp_int,
the struct classes' -O0 instruction counts); register-passed sources were
never the promotion's surface.

## FAILURES INVENTORY (conversion-first; reproductions in the artifact dirs)

1. **-O0 strict: fn_table_disp, nested_struct, sret_big, struct_by_value**
   (the struct-copy class). Mechanism (sret_big, diagnosed to the
   instruction): build's 12-copy stores execute behind a lifted `jne`
   (the i128 overflow-flag modeling of the loop's `jle`); at runtime the
   copy block is skipped and the sret cell stays zeroed
   (watchpoint-verified: the cell's only write is its own address).
   Repro: `bash scripts/semantic/run_semantic.sh /home/tovpr/tm-battery/t4/corpus /home/tovpr/tm-battery/t4/emit-o0 /home/tovpr/tm-battery/t4/sem-o0`
   ; runtime: `gdb -batch -ex "break build" -ex run -ex finish -ex "x/3gx <sret-cell>" /home/tovpr/tm-battery/t4/sem-o0/out_sret_big_lifted`.
   The four share the struct-by-value/sret copy shape.
2. **-O0 opt-safety: array_local** joins the four under `opt-21 -O2`
   (passed strict; fails under opt — new for this binary).
3. **-O2 pinned regressions: fizzbuzz_safe (SIGILL — the L1 poison-arm
   class), spill_many (SEGV)** — both passed the -O2 lift pre-T4; the
   promotion/regions changes at the -O2 frame layout re-opened them.
4. **-O2 new sources: fn_table_disp (541 vs 604), jump_table_sw** —
   first -O2 measurement; fail.
5. The eight pre-existing unit failures are unchanged (owner triage).

Per the conversion-first protocol none of these were patched with
per-shape machinery; they await the orchestrator's after-the-model-change
triage. Suggested first dig for the struct-copy class: the i128
overflow-flag guard the lifter emits for `jle` (the copy's `jne 401631`)
and the copy block's reachability, then struct_by_value's -O2 register
args.

## Risks / handoff

1. The -O0 strict gate is red for the four struct-copy binaries — the
   merger must weigh the inventory before merging; the pin/golden moves
   (va_arg_vacopy improvement; fizzbuzz_safe/spill_many -O2 regressions)
   are the merger's commits per the re-baseline rule.
2. The twin eagerly loads all N window slots — a foreign (non-lifted)
   caller of an address-taken promoted sub supplies a garbage window and
   could fault where the binary read garbage stack (not exercised by the
   corpus; flagged by the design's UB position on unpassed args).
3. `values_served` (the escape closure) is intentionally strict: ANY
   escaping stack value (including a window base passed to a
   thunk/variadic callee) joins Frame. The convergence table shows this
   costs little (the prize rows still moved).
4. The -O0/-O2 reference emissions for byte-identity checks are
   `/home/tovpr/tm-battery/t4/emit-o0` and `.../emit-o2`.
