# T3c — verdict: the single-predicate conformance; the escape dies entirely

Landed 2026-09-10 on `tm/t3c-single-predicate`. Final provenance:
`src=e7b3c1c9db41c52b` `bundle=54e284d5d3441228` (recorded after the
last install). Battery artifacts: `/home/tovpr/tm-battery/t3c/` (the
pre-T3c baseline emissions there were verified byte-identical 33/33 to
the merge-t3 reference BEFORE any change — the lane's comparison base).

## The directive, as finally scoped (owner, three refinements this session)

1. NO `is_seed`, NO SP-derived closure — ONE predicate `is_stack_access`
   over the denotation.
2. Remove EVERY other mechanism (strengthened mid-lane): audit
   `st_tag_of`, `outgoing_arg_stores`, written-in-block heuristics,
   seed-flag machinery; clean everything orphaned.
3. **The escape dies ENTIRELY** (final scope line): `frame_escapes` /
   `frame_escaped` are not rebuilt as denotational facts — DELETED.
   Consumers read the denotations directly. Failures are inventoried,
   not patched, not ticketed ("the model will change significantly
   anyways").

An interim state of this lane (commit `d4c7e68`) rebuilt
`frame_escapes` as a denotational disjunction; the final tree DELETES
it. The interim's measurements are preserved below where they are the
evidence for a decision.

## The deletions (each with a no-caller proof)

`src/hike_stack_model.ml` unless noted. After the deletions, the grep
set `{sp_derived_closure, sp_escaped, frame_addr_alias, def_facts,
def_facts_of_sub, is_memory_shape, value_free_vars, exp_escapes,
call_arg_escapes, store_data_escapes, frame_escapes, frame_escaped,
call_args_escape, unservable_stack_access-as-escape, has_outgoing_stack_args,
outgoing_arg_stores, sp_displacement, bounds_of}` is EMPTY over
`src/ test_cbat/ zz_scratch_probe/` (`*.ml *.mli`) except the verdict's
own prose.

- **`sp_derived_closure`** — the {SP}-seeded syntactic closure; sole
  callers were the deleted `sp_escaped`/`frame_addr_alias`.
- **`sp_escaped`** (`call_arg_escapes` + `store_data_escapes` arms) —
  the syntactic escape.
- **`frame_addr_alias`** — the untagged-through-frame-var veto; defined
  over the closure.
- **`def_facts` + `def_facts_of_sub`** — only the arms above consumed
  the map; `has_outgoing_stack_args` was rewritten to per-def
  extraction (and then deleted with the escape).
- **`is_memory_shape`** — only `def_facts`/`sp_escaped` consumed it.
- **`frame_escapes`, `call_args_escape`, `unservable_stack_access`
  (escape form), `has_outgoing_stack_args`, `is_real_call`** — the
  interim denotational escape and its inputs; the final scope deleted
  the whole entry. `is_real_call` had no other caller.
- **`outgoing_arg_stores` + `sp_displacement` + `bounds_of`**
  (`src/cbat_vsa/cbat_vsa.ml` + `.mli`) — the pushed-arg set fed only
  `frame_escapes`; `sp_displacement`/`bounds_of` fed only it. The
  whole chain is caller-less now.
- **`vsa_info.frame_escaped`** (`src/convutils.ml`) — the field, its
  `equal` conjunct, and the `mk_vsa_info{,_maps}`/`empty_vsa_info`
  parameters. All 15 test/probe constructor sites updated.
- **`hike_vsa.ml`**: the per-sub escape computation block deleted.

**The one interface growth** (not a deletion, recorded): the model's
partition now READS the denotations — `regions_of_sub ~sol sub info`
(`src/hike.mli` updated; `val denote_def`/`val denote_defs` moved from
the fixtures-only `Test_seam` to the production surface of
`cbat_vsa.mli` — they were already re-exported in the .ml).

## What the consumers read now (the escape deletion's shape)

**The region partition decides from the tags and the denotations
alone.** `regions_of_sub ~sol sub info` computes each region's
`convertible` as: every member is a NEGATIVE singleton `Range` tag AND
the sub's stack traffic is region-servable — "region-servable" = the
access's tag is a convertible singleton; "stack-reachable" = an address
OPERAND's denotation is a stack-symbolic set (`is_stack_access`
applied to the operand's value at the def, state threaded with
`denote_def`). One predicate family; no var closure; no escape fact;
no `frame_escaped` anywhere.

WHY the servability clause exists (measured, three times this lane):
in the LANDED T3 emitter, a precise sub's stack traffic flows through
the SP-relative lane, whose anchor is the caller-threaded
`hike_stack` (the caller's frame neighborhood) or — for the entry sub —
was `undef` until this lane bound it to the real machine stack pointer
(`llvm.stacksave` at entry; the pre-existing latent hole that
array_local/sret_big tripped with a segfault). Neither anchor is
PRIVATE per sub, so a precise sub carrying unservable traffic (an
untagged runtime-indexed access — union_overlap's `u[i]`; a
non-singleton span) reads/writes caller-shared or undefined memory.
The frame model's anchor is the sub's own frame cell — private — so
unservable subs keep Frame. THE OWNER'S T4 DIRECTIVE ("SP binds to an
entry-block alloca") makes every sub's SP neighborhood private and
dissolves this clause; the clause is written to be DELETED by T4, not
extended.

## Conformance audit (the strengthened mandate's targets)

| target | verdict | evidence |
|---|---|---|
| `st_tag_of` | **CONFORMING, kept** | reads only the solution's per-block state met into the walking state — a pure derived view; the tag is that state's denotation relativized. |
| `outgoing_arg_stores` | **DELETED** | was predicate-gated and conforming, but its only consumer was the escape; the removal orphaned it (no-caller proof above). |
| written-in-block frame-keeping (`inspect_call`'s `written` → `call_abstraction_frame ~escape`) | **KEPT — the denotation does not suffice** | the written-fact distinguishes "program-passed unknown" (the whole-memory-top fallback must engage) from "never-passed garbage" in unused arg registers (all-regs variant ⇒ frame-keep dies corpus-wide; stack-only-filtered variant ⇒ unsound for TOP args). It sizes the frame-keep boundary; it does not classify stack accesses. |
| seed-flag machinery (`prove_nonneg`'s `has_seed` store-chain) | **ATTEMPTED, MEASURED, REVERTED** | the pure denotational replacement (operand's value set bounded, min ≥ 0) grew the runtest failure set 8 → 10 (L-D2, L-D6 red — the guard decoder's cell bound comes from the store-chain structure the flat denotation at the guard point does not carry). Reverted per the mandate's "wherever a denotation suffices"; the failure set returned to exactly 8. Now also a FAILURES-INVENTORY observation (below). |
| KEEP list: VLA matcher, `stack_address_of_rhs`, `relativize_opt`/`in_stack_segment` band arm | **untouched, confirmed** | different questions than stack-access classification. |
| `denote_imm_exp` naming | **CONFORMING** | the immediate-value denotation is the correct one for addresses; no change. |

## BLOCKED-BY T4 (the parameter convention owns these)

1. **The SP anchor.** The SP local of a precise sub binds to the
   caller-threaded `hike_stack` (shared with the caller's frame
   neighborhood) or, for the entry sub, the real stack pointer
   (`llvm.stacksave` — this lane's definedness fix). The owner's
   directive — SP binds to an entry-block alloca (private per-sub
   storage) — is the real fix; when it lands, the partition's
   servability clause deletes and the 21 re-framed subs below can
   re-convert.
2. **The caller-window materialization lane** (`caller_mem_access`,
   the `hike_stack` argument threading, the `is_main` signature
   exception, `restore_sp_after_call`): untouched; T4 makes
   caller-window reads real call parameters.
3. **The region lane is decorative for singleton cells** (measured on
   union_overlap main): the region arm builds GEPs, but every def's
   value flows through SP-relative materialization — the region
   allocas serve no traffic today. T4's alloca-anchored SP either
   makes the region GEPs the access path or deletes them.
4. **The guard decoder's non-negativity store-chain** (the reverted
   attempt): deletes when the denotation carries the cell bound to the
   guard point.

## FAILURES INVENTORY (observations only — no fix commitments)

No gate is red in the final tree except the pre-existing unit-suite
baseline. Observations, for the orchestrator's after-the-model-change
triage:

- `dune runtest` rc=1, failure set == the 8 pre-existing
  (E2eD-7/8, LM F1-NEQ, F1-FT ×2, F1-B1 ×2, F1-B3) — the owner's
  recorded baseline (they fail on the pristine tip). Repro:
  `dune runtest` in the worktree.
- The `known_nonneg_of` denotational replacement was measured red
  (L-D2, L-D6) and reverted in the same session; the mechanism stands.
  Repro of the observation: replace `prove_nonneg`'s consumers with the
  denotational min-elem test and re-run `dune runtest` (see git
  history of this branch for the exact patch).
- The interim pure call-arg escape rule (commit `d4c7e68` alone)
  measured 29/33 on the -O0 strict gate (array_local, sret_big,
  va_arg_mixed, variadic) — superseded by the full deletion + the
  partition's servability rule; kept on the record because it is the
  cheapest reproduction of the SP-anchor privacy class.
- C4b's fixture was restructured (the control gets its own sub) — a
  deliberate test update to the servability semantics, asserted in
  both directions now (control convertible=true; non-servable members
  block every region).

## Gate table (the final tree; runs in `/home/tovpr/tm-battery/t3c/`)

| gate | result |
|---|---|
| build, default + vsa-debug profiles | rc=0 ✅ |
| instrumentation blocker (exercised by both builds) | clean ✅ |
| referee (`clpequiv`) | **2,861,148 checks / 0 mismatches** ✅ |
| `dune runtest` | rc=1, failure set == EXACTLY the 8 pre-existing ✅ |
| -O0 emission (`run_corpus.sh /tmp/corpus`) | 33/33 rc=0 ✅ |
| -O0 structural asserts | **165 passed / 0 failed** ✅ |
| -O0 strict semantics | **33 PASS / 0 FAIL** ✅ |
| -O0 strict opt-safety | **33 PASS / 0 FAIL**, 0 CRASH ✅ |
| -O2 emission (`run_corpus.sh /tmp/corpus_o2`) | 33/33 rc=0 ✅ |
| -O2 structural asserts | 165 passed / 0 failed ✅ |
| -O2 pinned semantics | **29 PASS / 4 FAIL, failing set == golden list (4)** ✅ |
| provenance | `src=e7b3c1c9db41c52b` `bundle=54e284d5d3441228` ✅ |

**THE PIN MOVED (improvement, deliberate, in this branch):** the
strict -O2 harness flipped `fizzbuzz_safe` and `fptr_table` to PASS;
`scripts/semantic/o2_known_failures.txt` moved 6 → 4 (byte_copy,
union_overlap, va_arg_mixed, va_arg_vacopy), re-verified green.
These were the L1-residual (fizzbuzz_safe lifted-ud2) and L4
(fptr_table) classes; at the -O2 frame layout the affected subs take
the Frame model and the lifts match native.

## Emission deltas, itemized (honesty bar)

-O0: 19 of 33 binaries differ from the merge-t3 baseline; ALL per-sub
storage flips are one-directional — 21 subs LOST spurious precision
(regions N → 0, frame 0 → 1): `deep_chain@f10 (7),
deep_recursion@fib (4), factorial@factorial (4) + @inc (7),
fizzbuzz@fizzBuzz (4), fizzbuzz_safe@fizzBuzz (6), fptr_table@fn0-3
(5 each), landmark_loop_1000@main (3), list@main (1),
many_args@sum12 (7), mixed_fp_int@main (4), nested_calls@level5 (6),
nested_struct@sum_fields (10), setjmp_longjmp@deep_nested (8),
spill_many@hammer (31), struct_arr_dynidx@runtime_idx (2),
tail_callish@d (5), union_overlap@member_for (2)`.

Why: those subs were precise in the baseline only because the closure
happened not to fire on them, while carrying unservable stack traffic —
the baseline left their SP-relative lane anchored at undefined or
caller-shared storage and never tripped it. The servability rule
returns them to the frame model, whose anchor is private. Zero
precision gained at -O0 (the intermediate call-arg-only state's gains
were all in this unservable class). Corpus-wide -O0: inttoptr
172 → 176, selects 3 → 3.

-O2: 16 of 33 binaries differ (alloca_vla, bitfield_struct,
deep_recursion, factorial, fizzbuzz, fizzbuzz_safe, fptr_table,
landmark_loop_1000, list, many_args, mixed_fp_int, nested_calls,
printf, ptr_chain, setjmp_longjmp, struct_by_value) — the same
escape-deletion decisions at the -O2 frame layout. inttoptr 101 → 101,
selects 34 → 34. The two behavior-relevant ones (fizzbuzz_safe,
fptr_table) now PASS both strict harnesses.

## Convergence (reference: `/home/tovpr/tm-battery/merge-t3/conv.log`)

Semantic classification — 2 rows moved, both improvements:
- `fizzbuzz_safe`: -O2 model DIFF → **SAME** (101/253 → 87/250)
- `fptr_table`: -O2 model DIFF → **SAME** (61/59 → 61/64)

All other 31 rows keep their classification (27 SAME/SAME + byte_copy,
union_overlap, va_arg_mixed, va_arg_vacopy -O2 DIFF = the golden four).

Quality-dimension rows (i0/i2 post-opt) that moved:
deep_recursion 39/183→29/183, factorial 59/45→55/45,
fizzbuzz 64/59→63/59, landmark_loop_1000 15/5→14/5,
many_args 133/4→121/4, mixed_fp_int 126/4→136/4,
nested_struct 132/4→129/4, rmw_oob 41/40→52/40,
setjmp_longjmp 45/45→39/34, setjmp_loop 133/123→111/123,
va_arg_mixed 186/92→186/39, list 214/241→214/276.

## Risks / handoff

1. The 21 re-framed subs lose region-splitting precision until T4's
   entry-block-alloca SP anchor; the convergence table shows the frame
   model optimizes them well regardless (most quality rows improved).
2. `llvm.stacksave` is a new emission form (entry subs without
   `hike_stack`); opt-21 handles it (opt-safety 33/33). T4's anchor
   replaces it.
3. The guard decoder's non-negativity store-chain remains (the one
   measured exception); ~120 lines delete when the denotation carries
   the cell bound to the guard point.
4. `escape_diag` probe added under `zz_scratch_probe/` (debug-only,
   never installed): per-call-block operand denotations + the region
   plan with every member's tag and rhs — this lane's diagnosis tool.
5. AGENTS.md's validation block is NOT refreshed here (the merger's
   commit records the provenance and the new 29/4 pin state).
