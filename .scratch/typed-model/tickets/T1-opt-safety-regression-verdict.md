# T1 — verdict: the typed-model opt-safety regression

Ticket: `T1-opt-safety-regression.md`. Branch `tm/t1-opt-safety`, fix
commit `199a060` (on `775d616`). Worktree `/home/tovpr/hike-t1`.
Battery artifacts: `/home/tovpr/tm-battery-t1/`
(`emit_unfixed`, `emit_fixed`, `emit_unfixed_o2`, `emit_fixed_o2`,
`sem_*`, `semopt_*`, `conv_before.txt`, `conv_after.txt`, `bisect/`).

## The mechanism (evidence-backed)

`create_addr_ptr` (typed-frame arm) routed **every** runtime address
integer through `GEP frame (val - anchor_i64 + anchor_idx)`. The wrap is
runtime-correct for ANY `val` (the anchor is `frame + anchor_idx`, so
the address algebraically collapses to `val`), but it presents LLVM the
WRONG underlying object whenever `val` is not an offset into THIS sub's
frame.

The failing pair makes that concrete. `struct_by_value`'s
`modify_copy` returns a 64-byte struct by value: the ABI's hidden sret
pointer (RDI) points into **main's** frame. The callee pushes RDI and
reloads it for the return copy; the VSA tags the eight return-copy
stores NOTHING (`dump_tags`: the `mem` defs `%00000735`–`%000007c5`
carry `-`; the address is a reloaded register of unproven provenance).
Untagged defs take the identity arm (`mem_access` `None -> create_exp`),
so under the typed model those stores were wrapped as
`GEP frame_mod (%RDI_saved - %anchor_i64 + 24)` — stores whose LLVM
"based-on" object is the callee's own 32-byte alloca.

Under `opt-21 -O2` the inliner inlines `modify_copy` into `main`; the
inlined alloca is provably dead and, per LLVM's based-on model, those
wrapped stores write ONLY into it — so they are deleted. At runtime
they wrote `frame_main + 80..143`; `main`'s subsequent loads of the
sret region then read stale memory
(`result.a0=4 result.b7=32546` vs native `100 / 1014`).

Evidence chain:

1. The failing `-O2` artifact
   (`semopt_unfixed/out_struct_by_value_opt.ll`) shows the deleted
   stores and the hoisted-above-the-call stale loads in `@hike_main`,
   while the `hike_stack`-routed (inttoptr) accesses survived.
2. Minimal A/B (`bisect/patched_inttoptr.ll`): converting ONLY those
   8 wrapped stores in `modify_copy` to `inttoptr` makes the full
   `opt-21 -O2` result byte-correct. The wrapped stores are the exact
   miscompile site.
3. The offset-model reference (`/tmp/emit_l1_o0`) materialized the same
   stores as `inttoptr` (unknown address → maximally conservative for
   the optimizer) and was opt-green — the typed flip introduced the
   based-on lie, not the access itself.
4. Single-pass auto-bisect exonerated every pass (confirmed on this
   tree); the breaking combination needs the INLINER (dead-alloca
   reasoning) — incremental pipeline growth reached it via
   inline + DCE-class cleanup.
5. `nested_struct` is the same shape (`transform`/`sum_fields`
   by-value struct args/returns); its fixed emission is byte-identical
   to the offset-model reference too.

## The fix (the general rule)

The typed frame GEP now requires the producer's frame-residency proof —
the model's own Typed-Frame/Exception-Lane contract, applied at the one
rule every access goes through:

- `src/bil2llvm_mem.ml` (`create_def`): derives the license from the
  def's tag — `Range (lo,_) | Infinite (lo,_)` with `lo < 0` proves the
  rhs's accesses live in THIS sub's frame (the widened/loop class; the
  pre-existing lo<0 fallthrough arm keeps its typed form). Every other
  tag kind — `Unbounded` (TOP proves nothing), `VLA` (the dynamic
  alloca is not the frame), untagged (foreign pointers: the sret
  pointer, reloaded pointers) — keeps the license false.
- `src/convutils.ml`: carries the license (`frame_wrap_license`), set
  per def, scoped to that def's rhs emission.
- `src/bil2llvm_section.ml` (`create_addr_ptr`): the typed arm fires
  only when licensed; everything else materializes the identity —
  `inttoptr` of the address integer (the exception lane, ADR 0009).
  The indirect-call target (a code address, never frame-relative) now
  also takes the identity, as it always should have.

The dispatch is total per tag kind (the license match is a two-arm
total match with a `_ -> false` catch-all; no "cannot happen" arm, no
gate, no fallback — the identity materialization IS the sound rule for
unproven addresses). Effect corpus-wide (-O0): runtime-index frame
wraps 201 -> 72 (the licensed, genuinely frame-relative ones survive);
`inttoptr` 42 -> 171; 14/33 emissions changed; nested_struct and
struct_by_value became byte-identical to the offset-model reference
(which was opt-green for both).

## Gates (before -> after, all on this tree's fresh emissions)

| gate | unfixed | fixed |
|---|---|---|
| corpus emission (-O0) | 33/33 rc=0 | 33/33 rc=0 |
| `check_allocas.sh` | 165/0 | 165/0 |
| strict -O0 semantics | 33 PASS / 0 FAIL | 33 PASS / 0 FAIL |
| **strict opt-safety (-O0)** | **31 PASS / 2 FAIL** (nested_struct, struct_by_value) | **33 PASS / 0 FAIL** |
| -O2 corpus emission | 33/33 rc=0 | 33/33 rc=0 |
| -O2 semantics (pinned) | 33/33 today (see stale-pin note) | 33/33 |
| -O2 emission + opt-21 -O2 | 31/2 (same pair, same mechanism) | 33/33 |
| `dune runtest` | — | rc=1 with EXACTLY the pre-existing 8-check baseline (E2eD-7/8, LM F1-B1 x2, F1-B3, F1-FT x2, F1-NEQ) |
| clpequiv referee | — | 2,861,148 checked / 0 mismatches |
| vsa-debug profile build | — | rc=0 |
| plugin provenance | src=dd72e43a2c75abea bundle=818458b8d83db655 | src=88f1b4f3e9dbb7e3 bundle=f4b8f6684e9250ea (git=199a060) |

Reproduce-first check: the unfixed tree's fresh emission failed exactly
{nested_struct, struct_by_value} on the strict opt-safety gate — same
set as the recorded reference.

## Convergence report (nested_struct / struct_by_value)

`convergence_report.sh /tmp/corpus /tmp/corpus_o2 <lift_o0> <lift_o2>`
(o0model/o2model = semantic class of the opt-21 -O2 result vs native;
i0/i2 = instruction counts):

| source | before (unfixed) | after (fixed) |
|---|---|---|
| nested_struct | DIFF / DIFF, 125/125 | **SAME / SAME**, 137/137 |
| struct_by_value | DIFF / DIFF, 141/141 | **SAME / SAME**, 187/187 |

Both lifts now converge to results equal to native; the instruction
counts rise slightly (the honest inttoptr materialization folds less
than the — unsound — wrapped GEP did). Full tables:
`conv_before.txt`, `conv_after.txt`.

## The -O2 pin: stale on the base tree (owner decision, untouched)

`scripts/semantic/o2_known_failures.txt` (6 entries) does NOT reproduce
on today's base tree against `/tmp/corpus_o2`: the UNFIXED tree's
unoptimized -O2 lifts also pass 33/33 (verified by reinstalling
`775d616` and re-emitting — `emit_unfixed_o2`, `sem_unfixed_o2`). So
the -O2 red-list collapse is NOT attributable to T1; it predates this
lane (layout/environment drift of the stale-read class the pin was
recorded against, or a corpus rebuild since the last verification).
What T1 demonstrably changes is the ROBUST variant: with the consumer's
optimizer inserted, the unfixed -O2 lifts still fail 2/33
(nested_struct, struct_by_value — the identical wrap-lie mechanism),
while the fixed tree passes 33/33. The golden file is left untouched —
moving it is a deliberate re-baseline (this verdict supplies the
evidence).

## Open risks

- The licensed-wrap arm (`Range/Infinite lo<0`) still claims the frame
  for mixed spans (`lo < 0 <= hi`) — pre-existing behavior, unpinned,
  and T7/T3's uniform materialization subsumes it.
- A def whose rhs mixes a licensed access with a foreign nested access
  would license both (the producer emits no per-node tags). No such
  shape exists in the corpus; the rule comment in `create_def`
  documents the boundary.
- The -O2 33/33 without opt is luck-dependent for the base tree (stale
  reads that happen to hit fresh values); the fixed tree removes the
  producer of those stale reads for the 14 changed binaries.
