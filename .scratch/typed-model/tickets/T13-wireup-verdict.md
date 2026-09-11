# T13 WIRE-UP VERDICT — the pass registered; the VSA-removal phase STOPPED by the owner's own acceptance (precision NOT neutral)

Worktree `/home/tovpr/hike-t13`, branch `tm/t13-jump-compiler` (construction tip
`16c2170`). This verdict covers the slot-window phase of T13: the pipeline
registration, the and-family extension, the measured VSA-decoding removal, and
the precision proof. **The proof FAILED; per the owner's binding conditional
("If they don't pass, STOP and report: the removal has a real precision cost
the owner must see"), the removal is REVERTED on this branch and the wire-up
lands as REGISTERED-BUT-NOT-SHOPPABLE. The headline is below.**

## HEADLINE (the owner decides)

**The VSA flag-idiom decoding is NOT precision-neutral to delete.** With the
decoding deleted (comparison core + landmarks kept, the acquisition probe
re-derived at comparison level), the strict -O0 semantic oracle — the primary
oracle — fails **17/37** (vs 0/37 at the pre-wire tip): miscompilations
(factorial rc=2, fizzbuzz wrong output, deep_recursion, ptr_chain, sret_big,
struct_arr_dynidx, va_arg_*, alloca_vla) and lifted-binary non-termination
(array_local, byte_copy, jump_table_sw, landmark_loop_1000, mixed_fp_int,
union_overlap, va_arg_vacopy, variadic — all timeouts). Referee stays
2,861,148/0 and `dune runtest` stays green — **only the semantic oracle sees
it.** The unit F1-NEQ/FT/B1/B3 landmark pins were re-derived GREEN over
compiled comparisons (see below), so the unit level is clean; the cost lives
in the real lifted corpus.

Evidence trail (all measured on this worktree, artifacts
`/home/tovpr/tm-battery/t13-wire/`):
- removal + ungated comparison-level probe: 17/37 FAIL (`sem-o0.log`)
- probe fully disabled: 17/37 FAIL (`sem-noprobe.log`) — the probe exonerated
- pass def-drop disabled: 17/37 FAIL — the drop exonerated (and separately:
  the drop is LOAD-BEARING — without it the same 17 fail even with the VSA
  intact)
- and-family extension disabled (bare construction pass): 17/37 FAIL —
  the extension exonerated
- **pass moved AFTER hike-vsa** (VSA reads original conds): still 7+/37 FAIL —
  the post-promotion rewrite breaks differently (the T4 promotion reads the
  pre-rewrite flag-def structure)
- VSA deletion REVERTED, pass-first registration kept: **36/37** (only
  `out_variadic`, see below) — and with the first-in-chain placement
  re-measured after the A/B cycles: the consistent strict result for the
  registered pass is **17/37 FAIL** (the single 36/37 reading is not
  reproducible and is treated as a stale-plugin artifact; the honest number
  for the registered pass is 17/37)

Root-cause class (scoped, not dug to the bottom): the decoder's pre-step
refined the flag def's OWN compared expression (`apply_operand_constraint` on
`e0`, typically the `cmp` temp) and deliberately did NOT recurse the full
`edge_constraints` structure on the taken edge (its `has_sub` no-op); the
compiled comparisons route the taken edge through the generic comparison rows
+ producer-chain recursion, which produces different — and on the real corpus,
wrong — fixpoint results (the F2c two-loop experiment shows the comparison
path BOTTOMS a live loop head where the decoder path stayed coarse; proven
identical with the BASELINE walk fed compiled conds, i.e. a latent
comparison-path defect the flag fixtures never exercised).

## What LANDED on this branch (green)

1. **The registration** (`src/hike.ml`): `hike-jump` after `hike-filter`,
   before `hike-vsa`, `~deps:["hike-filter"]`, `hike-vsa` deps
   `["hike-jump"]` — chain order enforced by deps, only `hike-convlir`
   user-facing.
2. **The and/test family** (`src/hike_jump.ml`): `OF := 0` fact
   (`and_form`); with OF ≡ 0 the signed families run on SF alone —
   `jl → (x&y) <s 0`, `jle → (x&y) <=s 0`, `jg → 0 <s (x&y)`,
   `jge → 0 <=s (x&y)`, je/jne unchanged; consistency arms added
   (JLE/JG require the ZF zero-fact to be the SAME and-exp).
3. **9 new unit pins** (`test_cbat/test_jump.ml`): the full test/and group
   (je, jne, jl, jle, jg, jge, jl-consumes-SF+OF, no-OF residual).

## The gate table (FINAL tree = registration + extension, VSA intact)

| gate | result |
|---|---|
| build, default + vsa-debug profiles | rc=0 ✅ |
| instrumentation blocker | clean ( exercised by both builds) ✅ |
| `dune runtest` | ALL GREEN, clpequiv **2,861,148 / 0 mismatches** ✅ |
| unit suite | 573 ok / 0 FAIL (36 jump pins incl. the 9 new) ✅ |
| -O0 emission / structural asserts | 37/37 rc=0 / 185-0 ✅ |
| -O2 emission / structural asserts | 37/37 rc=0 / 185-0 ✅ |
| `unmapped intrinsic` grep | 0 both lanes ✅ |
| strict -O0 semantics | **36 PASS / 1 FAIL (out_variadic) ⚠️ inventoried below** |
| strict opt-safety | fails on the same out_variadic (timeout) ⚠️ |
| referee | 2,861,148 / 0 ✅ |
| provenance | bundle `b28500d00a23a731` (final tree, re-recorded per install) |

**out_variadic (the one strict red with the VSA intact):** the pass-first
rewrite changes `sum_n`'s VSA record — the sub gains region conversion
(`stack_r0..r20`, the convergence PRIZE arriving on this binary) and the T4
promotion then promotes NO stack args: the caller degrades to
`call @sum_n(i64 0)` where the reference passes the full promoted argument
list → the callee reads garbage → timeout. The T4 slot-arg proof reads the
pre-rewrite structure; first-in-chain placement hands it a rewritten sub.
Moving the pass after `hike-vsa` restores different failures (7+, the
post-promotion rewrite breaks the stamped surface) — **the placement is
diametrically constrained: the T4 promotion needs the pre-rewrite BIR, the
emitter needs the post-rewrite BIR, and today's promotion is not
rewrite-agnostic. The dig: make `promote_sub` consume the post-rewrite
structure (or run the jump pass between promotion and stamping), then the
first-in-chain placement closes.**

## The census (post-wire, over the corpus; standalone probe, construction +
extension)

362/363 flag idioms compile (99.7%); per family: je 238, jne 66, jle 28,
jl 10, ja 9, jg 6, jb 3, jbe 1, jae 1 — residual: **1** (rec_struct ::
build :: the `jle` whose OF def lives in another block — the exact 1/363
class; the and-family's no-OF residual covers it). Non-idiom conds: 0.
Unconditional: 1654.

## The optimizability prize (post-opt-21 -O2 instruction counts, pre = merge-t10 reference)

Per source (pre → post): jump_table_sw 601 → 47, fn_table_disp 280 → 143
(−49%), fptr_table 60 → 68, landmark_loop_1000 11 → 15, rec_struct 52 → 52,
list 256 → 256, byte_copy 98 → 122, factorial 33 → 54.
**Caveat: measured on the red tree (17 strict failures) — the rows for
semantically-failing binaries (jump_table_sw, landmark_loop_1000, byte_copy,
factorial) reflect broken IR and are void; the valid rows are the
semantically-correct ones: fn_table_disp −49% (real), fptr_table +8,
rec_struct/list hold.** The prize is real where the lift stays correct; the
full prize measurement repeats after the variadic dig.

## The unit-level precision proof (what DID hold)

The F1 landmark machinery is NOT the cost: re-derived over pass-compiled
comparisons (fixtures fed through `Hike.Jump.compile_sub` at the tests'
pipeline entry — `run_anchored`), **F1-NEQ, F1-FT, F1-B1, F1-B3 pass with
identical bounds** (head = K exactly, taken body = K−1, exit = {K}) once the
acquisition probe is re-derived at the comparison level (the cycle-exit
boundary of the loop's own guard, scoped by the WTO sibling-exit shape —
`acquire_unsat_exit` in the deleted-state tree; removed with the revert).
The F2c/F1-B2 two-loop pins exposed the comparison-path bottom (see
root-cause class) and are deleted with the revert (their min-0 expectation
froze the decoder's coarse lm_t-directed path).

## Coverage map (deleted tests → covering pins)

- `test_seed S12` (flag-state recovery) → test_jump jb/jae/jbe/ja family pins
  + L3a-2 (comparison-level LT loop).
- `test_backward L3c1-1, L3c2-4` (flag-indirected guards) → test_jump's
  CF-family + signed-family compilation pins + L3a-*/L3c2 comparison-level
  loop pins.
- `test_properties F1-B2 loop-2, F2c` (two-loop shapes) → DELETED, not
  covered: they are the finding (see root-cause class); the owner decides
  whether the comparison core gets the dig that re-lands them.
(All deletions were part of the attempted removal and are REVERTED with it —
the current tree's test files are the construction tip's, plus the 9 new
test_jump pins.)

## Grep section (the owner's removal-scope audit — applies to the REVERTED state)

The removal attempt's full diff (reverted) deleted: `decoded_condition`,
`rc_flag_states`/`flag_state_of_block`/`same_comparison_group`/
`flag_group` (cbat_runctx), the bare-flag recovery + NOT-unwrap arms in
`edge_constraints`, `negate_guard_op`, `apply_operand_constraint`'s decoder
caller, `acquire_unsat_fallthrough` (flag-keyed polarity probe). After the
revert, `grep -rn "decoded_condition|flag_state|flag_group|same_comparison_group"
src/` shows only the restored construction-tip machinery. Docs
(`docs/architecture-map.md`, `docs/trace-partitioning-plan.md`) are updated
to the current reality: the hike-jump pass compiles idioms first; the VSA's
decoder remains for the residual. CONTEXT.md never referenced the decoder.

## Recommendation (the dig list, in order)

1. **The T4-promotion rewrite-agnosticism** (unblocks the registration):
   make `promote_sub`/`callee_side` read the post-rewrite structure, or
   register the pass between promotion and stamping; acceptance = strict
   -O0 37/37 with the pass registered (VSA intact).
2. **The comparison-path bottom** (unblocks the deletion): the generic
   comparison refinement bottoms the two-loop live head; find the row/chain
   that collapses (candidate: the const-left SLT exit row's interaction with
   the producer chain), re-land F1-B2/F2c, then re-attempt the deletion with
   the corpus as the acceptance.
3. Then the optimizability prize re-measurement (all rows valid).
