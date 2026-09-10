# T4b — verdict: conversion correctness constructed (the -O0 oracle is green)

Landed 2026-09-10 on `tm/t4b-conversion-correctness` (worktree
`/home/tovpr/hike-t4b`), branched at the T4-merged tip `f71e960`. Final
provenance: `bundle=06b009e387d37dc3` `src=f2c755c6af6e6269`. Battery
artifacts: `/home/tovpr/tm-battery/t4b/` (`emit-o0`/`emit-o2` are the NEW
reference emissions; semantics `sem-o0`, `semopt-o0`, `sem-o2`; logs
`runtest.log`, `conv.log`, `allocas-o0/o2.log`).

**Strict -O0 semantics: 37 PASS / 0 FAIL (was 32/5 at the T4 merge).**
Strict -O0 opt-safety: 37/37 (array_local's opt failure resolved too).
The -O2 pin shrank 9 → 7 (fn_escape, fn_table_disp flip green, proven).

## What was wrong — the corrected diagnosis

T4's verdict attributed the struct-copy class to "the lifted i128
overflow guard skips build's copy". That diagnosis is superseded: the
guard is CORRECT (the `jle` → `ZF | SF^OF` lowering branches the right
number of times; verified in the emitted IR). The stores were lost to
STORAGE SPLITTING, not control flow. Both -O0 classes were holes in
rules, each fixed at the point the wrong value is produced.

### Class A — the struct-copy class (nested_struct, sret_big, struct_by_value)

**Mechanism (sret_big `build`, watchpoint-grade):** the loop's array
store `mem[RBP + (sext(i)<<3) - 128]` is a stack access whose address
denotation the fixpoint LOSES (the -O0-spilled counter widens to TOP in
the memory-cell lane; `sext(i)<<3` follows it). `is_stack_access`
answered false → the def carried NO tag → `extract` never seeded it →
the partition never saw it. The copy-out's loads of the SAME cells
(`Range(-144,-144)` … singletons — the addresses are `RBP`-constant
there) DID seed; `regions_of_sub` merged them into singleton regions;
`stack_to_locals` converted them to zero-initialized slot locals; the
loop store emitted through the raw `inttoptr` lane — writing real
storage while the copy-out read the zeroed locals. The checksum read
zeros. Two storages served cells one access-family touches: exactly the
split-storage shape the Region Base term declares unrepresentable, but
reached through the tag-INVISIBLE back door.

### Class B — the indirect-call -O0 class (fn_escape, fn_table_disp)

**Mechanism (fn_escape `e_two`, verified to the instruction):**
`callee_side` promotes per DEF: any def whose rhs CONTAINS a load at a
proven slot offset enters `prom_slots`. `mem_access`'s Caller arm then
replaced the WHOLE DEF with the bare slot parameter. `e_two`'s
`EAX := EAX ^ mem[rbp+0x10]` (tagged `Caller(8,8)`) became `slot0` —
the xor and the `b` operand vanished (RSI dead in the IR); the machine
computes `b ^ g`. The window/thunk packing itself was verified correct
end-to-end (window = the callee's entry RSP; slot i at window+8+8i; the
push-modeled outgoing cells land exactly there).

**Class B' — the caller side of the same class (nested_struct,
struct_by_value, and the tail of fn_escape's +1):** the site's slot
argument was the store's data EXP re-evaluated AT THE CALL.
`fr.outgoing` stored `(slot i, data exp)`; `create_call_args` ran
`create_exp` on it at the jmp — reading the data VAR's value AFTER the
block redefined it. nested_struct's `transform` call passed cell2's
value for slot0 AND slot2 (`%132, %120, %132`): the outgoing stores'
data vars were `RAX, RDX, RAX`, and `RAX` had been redefined by the
cell2 load before the call. struct_by_value's 8-slot struct pass was
garbage the same way.

**Class A' — the written-slot inconsistency (struct_by_value's
remaining red):** modify_copy's `s.a0 += 100` is a store INTO the
caller's slot cell (the window lane — correct), but the copy-out's
reload of that cell still promoted to the STALE parameter (`result.a0`
read 0+100=0-way wrong). A slot cell the sub WRITES must be read
through the same storage the write used. The sub-slot variant: `s.b7
+= 999` writes at entry_rsp+68 — INSIDE slot 7's cell but not at its
base — so slot-index arithmetic missed the alias entirely
(`result.b7` stayed 15).

## The constructed rules (where each sits; the case-count delta)

1. **The Unknown class seeds (producer, `cbat_vsa.ml` `extract`).**
   The address denotation's trichotomy is now TOTAL:
   stack-symbolic → tag (unchanged); provably-foreign (a section
   constant) → untagged real-address lane (unchanged); **unknown (TOP)
   → `Unbounded`** — it may name this frame, so `accesses_served`
   reads it and the storage lattice joins the sub to Frame: ONE
   storage, every access served. No new emitter rule — the
   `Unbounded` kind's existing lane (warn-once + raw) already is the
   complete rule; the producer just stopped conflating unknown with
   foreign. The 100% Tagging Invariant now holds for the TOP class.
2. **The Caller lane serves the NODE, not the DEF (emitter,
   `bil2llvm_mem.ml`).** One rule over the def's mem node and its
   fact: a proven slot read is its promoted parameter (coerced to the
   node's own width — the narrower-read rule); the retaddr cell reads
   undef; anything else takes the window materialization. The node's
   value is substituted into the rhs (`rewrite_mem_node` — the shared
   mapper the pointer lane already used), so the def's surrounding
   computation is carried BY CONSTRUCTION. The two whole-def
   replacement arms are DELETED.
3. **The slot argument is the value the store WROTE (emitter,
   `bil2llvm.ml` + `bil2llvm_mem.ml` + `bil2llvm_calls.ml`).**
   `create_def` records the emitted value of every def that is a
   site's store (`fr.store_vals`, keyed by the storing def);
   `create_call_args` looks the value up by the site's (slot, def)
   pair. The late evaluation machinery (`def_term_of`, the
   `store_data_of_rhs` extraction, the exp re-emission at the call) is
   DELETED. Requirement this exposed and fixed: the Store lanes'
   VALUE is the stored data — `create_store`/`const_addr_store`/
   the rip-relative fallback returned the void store instruction (a
   type-hole: Bil.Store's exp value IS the data) — three sites now
   return the data.
4. **A written slot demotes (producer, `hike_vsa.ml` `callee_side`).**
   A Caller store marks every slot cell its bytes intersect (base or
   sub-slot offset, single- or multi-cell) as written; the written
   slots leave `prom_slots`, so their reads — and every other access —
   take the window, where the write landed. The parameter is only ever
   the initialization of a read-only slot. `prom_window` was already
   true for any storing sub (unchanged); `prom_arity` stays the
   positional interface (params for positions below max, reads or
   not).

### The case-count delta (the owner's measure)

Deleted: the two whole-def replacement arms (promoted / retaddr) in
`mem_access`; the late site-data evaluation path (`def_term_of` map,
the rhs data extraction, the call-time `create_exp` — ~25 LOC); two
duplicated per-node mapper classes (folded into the shared
`rewrite_mem_node`); the void-returning Store-lane anomaly (three
return sites made one rule: the form's value is the data); the
implicit — and unsound — case-fusions "TOP address ⇒ provably foreign"
and "a written slot's reads still take the parameter" (each was the
absence of a case, not a case).

Added: the Unknown→`Unbounded` seeding arm (one rule over the
denotation's third class); the written-slot demotion marking (one
rule over the record's offsets + the store's width); the
store-value recording (one `EHashtbl.set` at the def's emission).
Zero gates (no conditional refusal anywhere), zero shape tests, zero
"cannot happen" arms. Net src diff: 176 insertions / 94 deletions
(~60 of the insertions are the rules' documentation comments); the
F1-2 fixture pin re-derived (it froze the old unsound not-seeded
behavior of the TOP class — the T8 precedent).

## Gate table (the final tree)

| gate | result |
|---|---|
| build, default + vsa-debug profiles | rc=0 ✅ |
| instrumentation blocker | clean (rc=0) ✅ |
| referee (`clpequiv`) | **2,861,148 checks / 0 mismatches** ✅ |
| `dune runtest` | 516 ok; failure set == EXACTLY the 8 pre-existing (E2eD-7/8, LM F1-*); F1-2 re-derived ✅ |
| -O0 emission / structural asserts | 37/37 rc=0 / 185 passed 0 failed ✅ |
| **-O0 strict semantics** | **37 PASS / 0 FAIL** ✅ |
| -O0 strict opt-safety | **37 PASS / 0 FAIL** ✅ |
| -O2 emission / structural asserts | 37/37 rc=0 / 185 passed 0 failed ✅ |
| -O2 pinned semantics | **30 PASS / 7 FAIL — set == the updated golden seven; PIN SHRANK 9 → 7** ✅ |
| convergence vs merge-t4/conv.log | six rows moved to SAME/SAME, none moved to DIFF ✅ |
| provenance | bundle `06b009e387d37dc3` ✅ |

## The -O2 pin, re-attributed per member (current symptoms)

| member | symptom (this tree) | attribution |
|---|---|---|
| byte_copy | value divergence (ck1/ck2), rc=0 | L3 SSE lane def-use — T5 |
| union_overlap | value divergence (total), rc=0 | L3 SSE lane def-use — T5 |
| va_arg_mixed | SIGILL (rc=132) | L1 poison arm — the va_arg alignment-split dead branch reached at -O2 |
| fizzbuzz_safe | SIGILL (rc=132) | L1 poison arm — the T4-merge regression's symptom is the pre-T4 class; T5/L1 dig |
| va_arg_vacopy | last value 0 vs 6, rc=0 | the va_list state round-trip — T9 |
| spill_many | SIGSEGV (rc=139) | the -O2 frame layout under the promoted model — the T4-merge regression persists; needs its own dig (T5/inventory) |
| jump_table_sw | rc=192 (crash) | the -O2 indirect-JUMP dispatch (the jump-table goto lane) — its own dig |

fn_escape and fn_table_disp left the list (proven flips — they pass
-O2 strict). The pin file's comments carry this table; the golden +
AGENTS.md moved in this lane's commit per the re-baseline rule.

## Convergence (vs `/home/tovpr/tm-battery/merge-t4/conv.log`)

Moved to SAME/SAME (o0model/o2model): **array_local** (was
DIFF/SAME), **fn_escape** (DIFF/DIFF), **fn_table_disp**
(DIFF/DIFF), **nested_struct** (DIFF/SAME), **sret_big**
(DIFF/SAME), **struct_by_value** (DIFF/SAME). The promotion prize
held (many_args 58/4, mixed_fp_int 68/4, variadic 185/27,
nested_struct 95/4, struct_by_value 149/4, spill_many 134/4). No
source regressed. The remaining DIFF rows are exactly the pin's seven
(byte_copy, fizzbuzz_safe, jump_table_sw, spill_many, union_overlap,
va_arg_mixed, va_arg_vacopy — all -O2-side).

## FAILURES INVENTORY (anything still red)

1. The seven -O2 pin members above (the -O0 oracle, strict
   opt-safety, units, referee, both structural-assert gates are
   green).
2. The 8 pre-existing unit failures (E2eD-7/8, LM F1-*) — unchanged,
   owner triage (the T8 triage stands).
3. Re-baseline note: -O0 emissions 20/37 byte-identical to merge-t4's
   reference (17 changed — the Frame-joined subs + the promotion
   lanes); -O2 28/37 identical. The new reference emissions are
   `/home/tovpr/tm-battery/t4b/emit-o0` / `emit-o2`. The Unbounded
   diagnostic now fires once per sub whose pointer-arg derefs join
   Frame (27 -O0 lines, was 1) — the sanctioned channel reaching the
   TOP class; rc gates unaffected.

## Risks / handoff

1. `spill_many` (-O2, SEGV) is the only T4-merge regression whose
   mechanism is still undug; it is the first item for the next lane.
2. The Frame-joined subs carry the 64K window-sized frames (the
   existing `frame_dims` unbounded rule) — correct, and opt-verified,
   but a convergence cost the next lanes can reclaim by sharpening the
   mem-cell widening (the counter's TOP is a mem-lane widening
   artifact; `sext(i)<<3` by constant is arithmetic the wordsets could
   carry).
3. The thunk's eager window-slot loads remain flagged (T4's risk 2,
   unchanged).
