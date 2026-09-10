# Typed-flag removal — verdict: the anchor storage is THE fact

Owner directive: *"The typed_model = false flag should be completely
removed from the code and any reference of it!"* There is no literal
`typed_model` identifier — the flag is `ctx.Convutils.typed_frame :
(Llvm.llvalue * Llvm.llvalue * int64) option ref`: its `None` state was
"typed mode off", and the off state must not exist in the code's
language. Landed 2026-09-10 on `tm/s10a` (worktree
`/home/tovpr/hike-s10a`), code commit `57ac3bf`. Provenance: tree
`/home/tovpr/hike-s10a`, `src=3ad30228f02bb1aa`,
`bundle=7fbbe50632fd613e`. Battery artifacts:
`/home/tovpr/tm-battery/typed-removal/`.

**ZERO behavior change, proven: corpus emission BYTE-IDENTICAL 37/37 on
BOTH lanes** vs the T4b references `/home/tovpr/tm-battery/merge-t4b/
emit-{o0,o2}` — per-file `cmp`, `out_*.ll` AND `err_*.txt` (0 diffs of
37+37+37+37; directory listings identical). This is the expected
result: the deleted arm was measured unreachable (S10a verdict §5:
zero fires), so its removal changes no output.

## 1. The constructed shape — ONE anchor fact, two consumers

The incoherence removed: `frame_wrap_license` proves "this address
lives in this sub's stack storage", but a PRECISE sub set
`typed_frame := None` — so a licensed def there fell to the
`match (None, true) -> _` arm and inttoptr'd over a proven-ours
address (measured ZERO fires — S10a §5 — but the arm existed, and the
flag's `None` was a behavior switch read at the materialization site).

The new shape: the **stack anchor** is one fact, computed once per sub
in `create_sub` (`src/bil2llvm.ml`), stored on the emit context
(`stack_anchor` in `src/convutils.ml`), and consumed twice:

1. **`create_addr_ptr`'s licensed GEP** (`src/bil2llvm_section.ml`) —
   the ONE match is on the license alone: licensed →
   `gep anchor_storage (word − anchor_i64 + anchor_idx)`;
   unlicensed → inttoptr (the Exception Lane, ADR 0009).
2. **The SP Slot's `stack_0`** (`src/bil2llvm.ml`) — binds the same
   anchor integer. T4's SP Slot used to recompute this fact (its own
   `match frame, regions` with its own `ptrtoint` of `stack_r0`);
   that second computation is deleted.

The anchor's totality over storage-carrying subs, as one match:

| sub class | anchor |
|---|---|
| frame sub (not precise; tags non-empty or degraded) | `Some (%frame, anchor_i64, anchor_idx)` — what `build_frame_anchor` always built |
| precise sub (region split, plan non-empty) | `Some (stack_r0, ptrtoint stack_r0, 0)` — exactly the value the SP Slot bound for precise subs |
| tag-free, non-degraded | `None` — the sub owns NO storage |

### Where the fact lives, and why not on `fr`

The ticket suggested the per-sub frame record (`sub_frame`). Rejected
with evidence: `create_addr_ptr` is reached from `create_exp`
(`src/bil2llvm_exp.ml`), and the exp lane carries no `fr` — the
address integer is materialized arbitrarily deep inside recursive
`create_exp` calls (mem_access's Range/Infinite arm passes only
`llvm_builder, blk_tid, exp`), so an `fr`-threaded anchor would put
`fr` on every `create_exp` signature for zero behavior change. The
emit context is the carrier `create_addr_ptr` already reads (it
fetches `emit_ctx_var` at the site) — one home, read at both
consumers (the SP Slot consumes the same let-bound computation in
`create_sub`, not a re-read).

### The never-queried-when-absent proof (the option's honesty)

`stack_anchor` stays option-typed because a tag-free sub genuinely
owns no storage — there is no honest total value. The absence is
structurally never queried:

- `frame_wrap_license := true` happens ONLY in `create_def`, and only
  for a `Range`/`Infinite` def tag (`src/bil2llvm_mem.ml`).
- A `Range`/`Infinite` tag on any def ⇒ `sub_info.offsets` non-empty
  ⇒ the sub is NOT tag-free ⇒ in `create_sub` either the frame arm
  fired (`frame = Some`) or `is_precise` held — and `is_precise`
  requires `stack_plan <> []`, so `regions` is non-empty and the
  anchor is the `stack_r0` arm. In BOTH cases `anchor = Some`.

So `anchor = None ⇒ license = false for every def of the sub ⇒ the
licensed arm never executes`. The argument is made executable as a
shape assert in the licensed arm (`failwith "licensed address in a
storage-free sub (no anchor)"` — the create_branches-class internal
assert on a producer-guaranteed invariant, per the repo's recorded
precedent), NOT as a behavioral fallback: no code path reads
"absent" as a mode.

### What "off" assignments died

- The unconditional per-sub `ctx.Convutils.typed_frame := None;`
  (the off-write) — DELETED. `create_sub` performs exactly ONE write,
  `ctx.Convutils.stack_anchor := anchor`, of the computed fact.
- The conditional `typed_frame := Some (Base.Option.value_exn frame,
  ...)` — DELETED (folded into the one write; the `value_exn` died
  with `build_frame_anchor`'s unboxing).
- The pre-first-sub initializer `stack_anchor = ref None` in
  `empty_emit_ctx` remains, commented as what it is: the empty record
  before any sub is emitted, not a mode — a ref needs an initial
  value, and no def emits before `create_sub` assigns.

## 2. Case-count delta (every deleted case)

| site | before | after |
|---|---|---|
| `create_addr_ptr` (`bil2llvm_section.ml`) | 2×2 match on `(typed_frame, license)`: `(Some,true)`→GEP; `_`→inttoptr conflating `(Some,false)`, `(None,true)` **(the incoherent licensed-but-inttoptr arm)**, `(None,false)` | ONE match on the license: `true`→GEP into the anchor storage; `false`→inttoptr. The incoherent arm cannot exist: a licensed address routes to the sub's ACTUAL storage (frame or stack_r0) |
| `create_sub` (`bil2llvm.ml`) | `:= None` + conditional `:= Some` (two writes, one off) | one write of the computed anchor |
| `create_sub` SP Slot | a SECOND anchor computation (`match frame, regions` + `ptrtoint` of `stack_r0`) | consumes the one `anchor` (2-arm match) |
| `build_frame_anchor` | returned `(Some frame, ...)`; caller `value_exn`ed | returns the frame unboxed; the option-mboxing and the `value_exn` deleted |
| `sub_frame` (`bil2llvm_env.ml`) | carried `frame` and `anchor_idx` — constructed, NEVER read (grep-proven orphans) | both fields deleted; `anchor_i64` stays (3 live readers: the stack0-fallback in `build_entry_block`, `caller_mem_access`, `mixed_mem_access`) |

Net: +63/−36 over 5 files.

## 3. Grep proofs

- `grep -rn typed_frame src/ test_cbat/ zz_scratch_probe/ scripts/
  docs/ CONTEXT.md AGENTS.md` (excluding `_build`, `.scratch`) →
  **zero hits**. The identifier survives only in historical lane
  records under `.scratch/` (S10/S10a verdicts describe the pre-lane
  tree; records are not rewritten).
- The blocker (`src/check_instrumentation.sh`) clean, rc=0.
- New name says what it is: `stack_anchor` — the sub's stack anchor
  storage (the `cbat_walk.ml` local of the same name is an unrelated
  in-scope-only binding in the vendored VSA; no collision).

## 4. Byte-identity

Per-file `cmp` vs `/home/tovpr/tm-battery/merge-t4b/emit-{o0,o2}`:

| lane | out_*.ll | err_*.txt | dir listing |
|---|---|---|---|
| -O0 | 37/37 identical | 37/37 identical | identical |
| -O2 | 37/37 identical | 37/37 identical | identical |

## 5. Gate table

| gate | result |
|---|---|
| build, default + vsa-debug profiles | rc=0 both ✅ |
| instrumentation blocker | clean, rc=0 ✅ |
| `dune runtest` failure set | **== EXACTLY the 8 pre-existing** (E2eD-7/8, LM F1-B1×2, F1-B3, F1-FT×2, F1-NEQ); set-level diff vs the S10a baseline: IDENTICAL ✅ |
| referee (forced `dune runtest --force`, `runtest-forced.log`) | **clpequiv: checked=2,861,148 mismatches=0** ✅ |
| -O0 emission | 37/37 rc=0 ✅ |
| -O0 structural asserts | 185 passed, 0 failed ✅ |
| **-O0 byte-identity vs `merge-t4b/emit-o0`** | **37/37 IDENTICAL** (out + err) ✅ |
| -O0 strict semantics | **37 PASS / 0 FAIL** ✅ |
| -O0 strict opt-safety | **37 PASS / 0 FAIL** ✅ |
| -O2 emission | 37/37 rc=0 ✅ |
| -O2 structural asserts | 185 passed, 0 failed ✅ |
| **-O2 byte-identity vs `merge-t4b/emit-o2`** | **37/37 IDENTICAL** (out + err) ✅ |
| -O2 pinned semantics | **semantic-pin: OK — failing set == golden list (the seven: byte_copy, fizzbuzz_safe, jump_table_sw, spill_many, union_overlap, va_arg_mixed, va_arg_vacopy)**; no movement ✅ |
| provenance | tree `/home/tovpr/hike-s10a`, git `57ac3bf`, src `3ad30228f02bb1aa`, bundle `7fbbe50632fd613e` ✅ |

Battery summary: the single hard red is the `dune runtest` rc gate —
the pre-existing 8-failure baseline makes rc non-zero by design
(identical to T4b's and S10a's battery records). Everything else
green.

## 6. Scope notes

- ADR 0009 / CONTEXT.md untouched: they name the TYPED FRAME *model*
  (the doctrine), not the flag; no `typed_frame` identifier appears
  in them.
- The precise-sub licensed-GEP route (licensed ⇒ GEP into `stack_r0`)
  remains zero-fire on this corpus (byte-identity is the proof); if a
  future corpus shape ever fires it, the form is the T1-correct one —
  right runtime value AND the right underlying object — so the
  disposition would be a precision note, never a correctness ticket
  (the S10a §5 reasoning now holds by construction rather than by
  measured absence).
