# T10 — verdict: the pipeline simplification (the filter dies; the emitter consumes NO record)

Landed 2026-09-11 on `tm/t10-pipeline` (worktree `/home/tovpr/hike-t10`), two
commits: part 1 `58b63e5`, part 2 `52e69e5`. Final provenance:
`bundle=daca4f03b8dc30fb` `src=5d698ee14e997280` (recorded against the
committed tip). Battery artifacts: `/home/tovpr/tm-battery/t10/`
(controls `ctrl-o0`/`ctrl-o2` lifted by the pre-T10 tip; part-1
emissions `emit-o0-p1`/`emit-o2-p1`; final emissions
`emit-o0-p2`/`emit-o2-p2`; semantics `sem-o0-p2`, `semopt-o0-p2`,
`sem-o2-p2`; allocas `allocas-o{0,2}-p2.log`; convergence `conv.log`;
the two part-1 semantic logs).

## Part 1 — the intrinsic-callers filter dies (commit 58b63e5)

`calls_intrinsic`'s predicate — `is_intrinsic && not
is_emittable_intrinsic && not is_llvm_x86_intrinsic` — was a
CONTRADICTION: `is_emittable_intrinsic` (intrinsic WITH a body) and
`is_llvm_x86_intrinsic` (intrinsic WITHOUT a body) partition the
intrinsics by body-ness, so no sub ever satisfied the predicate and the
set it built was always EMPTY. The exclusion was not a relic at risk of
misfiltering; it was dead code. Deleted: `calls_intrinsic`, the
`filter_set` plumbing, and the `Core.Set.mem` arm of `should_filter`.
What stays filtered: the intrinsic SUBS themselves (the bodyless BAP
`@intrinsic:*` placeholders — not code; call TARGETS map through the
emitter's table). The symbol-table check is general and stays.

Gates (part 1 alone): byte-identical 37/37 BOTH lanes vs the
same-tree control — the structural proof of deadness; emission rc=0
both lanes; the `unmapped intrinsic` grep CLEAN (the 09-02 gotcha, now
an explicit gate); check_allocas 185-0; strict -O0 semantics 37/37.

## Part 2 — THE EMITTER CONSUMES NO RECORD (commit 52e69e5)

### The BIR-rewrite construction (what the sub/call terms now carry)

`Hike_vsa.promote_sub` runs in the vsa pass (after the record fold, one
`Project.map_program`), consuming the SAME facts the emitter used to
read, at rewrite time:

1. **Promoted parameters are real BIR args.** The sub gains `arg_t`
   terms — `hike_slot0..arity-1`, then `hike_window` iff the
   Caller-Window Parameter survives — minted by the model's
   deterministic grammar. `compute_sub_sig`'s general branch appends
   `Term.enum arg_t sub` after the ranked register lanes: the signature
   transcribes the term. The written-slot demotion already lived in
   `callee_side` (demoted slots never enter `prom_slots`), so their
   loads are never rewritten and keep the window — EXACT T4b carry.
2. **Proven slot loads read their parameter.** A def in `prom_slots`
   (the `load_of_rhs` class: first mem node is a Load, no store in the
   rhs) gets its node replaced: `Var (arg_slot i)` at 64 bits,
   `Cast (LOW, bits, Var (arg_slot i))` narrower — the emitter's former
   trunc-to-node-width rule, now expressed in the BIR.
3. **Call sites bind stored values structurally.** Each site slot
   `(i, dtid)` gains a def `hike_argI := Var (lhs of dtid)` inserted
   immediately after the storing def. The emitter's `create_call_args`
   passes `get_local (call_arg i)` — the value the store WROTE (the
   storing def's own binding), never a later state: the T4b
   stored-value semantics BY CONSTRUCTION (`store_vals`/`fr.outgoing`
   deleted). `create_def` coerces the arg def's value to 64 exactly
   where the call used to coerce. The DCE keep rule roots the
   call-arg defs (`is_call_arg` — the load-roots precedent: the rule
   is defined over the vars the rewrite creates).
4. **Resolved indirect targets are direct.** A jmp in `prom_resolved`
   with `Some t` is rewritten to `Call.with_target (Direct t)` (tid and
   guard preserved); `cf_type` routes it to the plain direct-call arm.
   `create_indirect_call` reduces to the pointer-call class only
   (multi/foreign/unresolvable) — the `fr.resolved` dispatch deleted.
   Recorded behavior delta: a noreturn RESOLVED indirect call used to
   fall into cf_type's `Ret` arm (the call vanished); now it is direct
   and emits. No corpus site is in that class (fn_single's resolved
   sites have returns); the rewrite is the more faithful transcription.
5. **Per-def facts ride the DEF'S VALUE.** `Model.def_kind_slot` (a KB
   value slot on `Theory.Value.cls` — the `rip_relative_addr`
   precedent the emitter already consumes) carries the kind
   (`Range`/.../`Dead`), and the VLA marker for the dynamic-allocation
   defs (whose rhs is an SP decrement — no mem node, hence no tag —
   the marker travels in the same slot). The producer stamps once
   (`stamp_def_kinds`); the emitter's tag dispatch, frame-wrap
   license, and dynamic-alloca rule read `def_kind def`. `alloc_tids`
   and the record's `offsets` map leave the emitter.
6. **Geometry rides the SUB TERM.** `Model.layout_tag` (a registered
   `Value.Tag`; payload `Sub_layout { frame_bytes : int64 option;
   regions : (id, span, bytes) list }`) carries the alloca-construction
   inputs alone — `layout_of_sub` replicates the emitter's former
   frame decision exactly (precise → regions; tags-empty ∧ ¬degraded →
   no storage; else `frame_dims`). No offsets, no promotion facts, no
   kinds in it.
7. **The retaddr read stays an emission-time rule over the per-def
   tag** — BIR has no undef. The arm fires on `Caller (0,0)` + first
   node is a Load + width ≤ 64 + no store in the rhs: set-equal to
   `callee_side`'s `prom_retaddr` class, so the `prom_retaddr` set is
   deleted, not threaded.

Exemptions (exact-carry): the emittable intrinsics and `@main` skip the
CALLEE side (no BIR args, no parameter reads — their signature branches
are the free-var projection / fixed rdi-rsi, exactly as before). The
CALLER side (arg defs + direct targets) runs for EVERY sub — the first
build's `i64 undef` regression on factorial's promoted call from `@main`
was exactly this split done wrong, caught by the emission diff and
fixed before any semantic gate ran.

### The divorce proof (grep + module direction)

```
grep -n "Hike_kb\|info_of_sub" src/bil2llvm*.ml src/bil2llvm.mli   → no matches
grep -n "vsa_info|prom_slots|prom_arity|prom_window|prom_retaddr|
        prom_sites|prom_resolved|stack_plan|vla_alloc_tids|sp_extents|
        .offsets|degraded|regions_of_sub|split_plan|frame_dims"
        src/bil2llvm*.ml src/bil2llvm.mli                          → no matches
```

The emitter references `Hike_stack_model` only for the shared grammar
(var minting, the kind enum, the layout tag, `def_kind`) — never the
`vsa_info` record type. Dependency direction: `bil2llvm* →
Hike_stack_model → (KB slots declared there)`; `Hike_kb` is referenced
only by `hike.ml` (provide + the pipeline debug print) and
`hike_stack_to_locals.ml` (the fission rewrite) — pipeline passes. The
KB-vs-term-tag question for the record DISSOLVED: with the emitter out,
the record's readers are the producer's own downstream pipeline passes
(STL) and the fixtures, so `hike_kb` stays as the pipeline-only
carrier — one carrier, no emitter path reaches it.

### The re-baseline itemization (byte-identity NOT the gate; the oracle is)

- Part 1: 37/37 identical both lanes (the deadness proof).
- Part 2 -O0: 29/37 identical; 8 changed — deep_recursion,
  fizzbuzz_safe, fn_escape, fn_single, fn_table_disp, jump_table_sw,
  nested_calls, nested_struct (the promotion/resolution surface; the
  call-arg defs and direct targets re-shape the caller blocks' phi
  plumbing).
- Part 2 -O2: 34/37 identical; 3 changed — fn_escape, fn_table_disp,
  va_arg_vacopy.
- Diagnostics: identical tables (268 `hike:` lines in each log; the
  same families after number-normalization).
- Corpus size: 37/37 BOTH lanes (part 1 lifted no new subs — it could
  not; the filter was empty).
- Emissions: rc=0 both lanes; `unmapped intrinsic` grep CLEAN;
  check_allocas 185-0 BOTH lanes.

### The census reproduction (delta zero, same greps both trees)

| class | pre-T10 ctrl | T10 |
|---|---|---|
| thunk defines (`define internal … _hike_thunk`) | 26 | 26 |
| defines with slot params (`%hike_slot0`) | 26 | 26 |
| window-param defines (`%hike_window`) | 29 | 29 |
| pointer-call sites (`call { i64, i64 } %`) | 6 | 6 |
| fn_single resolved direct promoted calls | 2 | 2 |

(The absolute counts use this lane's grep definitions; the REPRODUCTION
claim is the delta-zero against the same greps on the pre-T10 control —
29 of 37 -O0 binaries byte-identical is the stronger form of the same
fact. The T4 verdict's "8 modules / 12 thunks / 64 sites" used narrower
greps; the site count now lives in the record the rewrite consumes, and
the construction is pinned by the new unit family.)

## Gate table (the final tree, committed)

| gate | result |
|---|---|
| build, default + vsa-debug profiles | rc=0 ✅ |
| instrumentation blocker (exercised by both builds) | clean ✅ |
| referee (`clpequiv`) | **2,861,148 checks / 0 mismatches** ✅ |
| `dune runtest` | 523 ok; failure set == EXACTLY the 8 pre-existing (E2eD-7/8, LM F1-*); +7 new T10 pins PASS ✅ |
| -O0 emission / structural asserts | 37/37 rc=0 / 185 passed 0 failed ✅ |
| -O2 emission / structural asserts | 37/37 rc=0 / 185 passed 0 failed ✅ |
| `unmapped intrinsic` grep (both lanes) | CLEAN ✅ |
| -O0 strict semantics | **37 PASS / 0 FAIL** ✅ |
| -O0 strict opt-safety | **37 PASS / 0 FAIL** ✅ |
| -O2 pinned semantics | **set == the golden seven** (byte_copy, union_overlap, va_arg_mixed, va_arg_vacopy, fizzbuzz_safe, spill_many, jump_table_sw), rc=0 ✅ |
| convergence vs `/home/tovpr/tm-battery/merge-t4b/conv.log` | **line-for-line identical — zero moved rows** (30 SAME/SAME + the seven DIFF) ✅ |
| provenance | bundle `daca4f03b8dc30fb` (the committed tip) ✅ |

## The pin (attribution-only; unchanged this lane)

byte_copy/union_overlap (L3 SSE — T5), va_arg_mixed/fizzbuzz_safe (L1
poison arm — T5), va_arg_vacopy (the va_list round-trip — T9),
spill_many (the -O2 frame layout — undug), jump_table_sw (the -O2
indirect-jump dispatch). No golden-list change; the pin gate green by
set equality.

## FAILURES INVENTORY (anything still red)

1. The seven -O2 pin members (above) — the pre-existing classes, all
   -O2-side; the -O0 oracle and opt-safety are green.
2. The 8 pre-existing unit failures (E2eD-7/8, LM F1-×6) — unchanged
   from the pristine tip (owner triage, the T8 triage stands).
3. Nothing else. No semantic or structural gate regressed; no new red
   was created or inherited.

## Doctrine accounting (the case-count delta)

Deleted from the emitter: the `Hike_kb.info_of_sub` reads (3 sites),
the `prom_slots`/`prom_retaddr`/`prom_sites`/`prom_resolved` dispatch
arms, `fr.outgoing`/`fr.store_vals`/`fr.resolved` (three sub_frame
fields and their recording machinery), `alloc_tids` threading, and the
`@main`/thunk record reads. Deleted from the filter: the dead
`calls_intrinsic` walk. Added: ONE rewrite (`promote_sub`), ONE stamp
(`stamp_def_kinds`), ONE layout computation (`layout_of_sub`), ONE KB
value slot, ONE term-attribute tag, ONE DCE root clause. The diff is
net-positive in lines (the layout payload's codec + the pin family
dominate) but the EMITTER's case count went DOWN: its per-sub inputs
reduced to layout + per-def tags, exactly the ticket's reduction.

## Handoff

- The fixture vocabulary changed for emitter tests: `stamp` (in
  `test_bil2llvm.ml`) replaces `Kb.provide` there; `Kb.provide` stays
  correct for pipeline-pass tests (stl/vsa/dce fixtures).
- The T10 probe (`prom_dump`) was used for the dig and deleted; the
  pins (`T10-PROMOTE`/`T10-SITE`) carry its facts permanently.
- T5/T9 inherit: the record is pipeline-only; any new emitter-facing
  fact must ride the term (def value slot or sub layout/tag), never a
  KB query.
