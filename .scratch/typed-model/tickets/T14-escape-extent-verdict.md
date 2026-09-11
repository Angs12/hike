# T14 — the escape-extent rule: VERDICT (landed 2026-09-10)

Branch `tm/t14-escape-extent` (worktree `/home/tovpr/hike-t14`), base
`1ae0f2e` (the T10 merge). Authority:
`T14-escape-extent-rule.md`. Battery:
`/home/tovpr/tm-battery/t14/battery-t14.summary` — **0 hard reds; the
pinned gate reports IMPROVEMENT: spill_many flipped green (pin 7 →
6)**.

## 1. The rule as landed (where it sits, what it answers)

**THE OWNER'S INVARIANT, now structural: only a `StackOff` denotation —
a value formed from THIS sub's SP — sizes the frame and decides
escape. Regular integers contribute NOTHING.**

- **The accessor.** `Cbat_clp_set_composite.stack_offsets : t ->
  Clp.t option` — answers ONLY for `StackOff offs` (`Some offs`);
  plain `Clp`/`FinSet` (including the in-band degraded arm) is `None`.
  This is the ticket's `stack_offsets` accessor; it already existed as
  the T3 accessor `as_stack` (same type, same contract) and is
  RENAMED to the rule's role — 3 sites (the .ml def, the .mli decl,
  one use in `cbat_walk.ml`'s `stack_anchor`). No alias, no
  duplication: the diff renames, it does not add.
- **The seam.** `note_escape` in `Hike_vsa.caller_side` (the escape
  probe's post-T10 home — the promotion classifier) now asks
  `Vsa.WordSet.stack_offsets ws` instead of
  `Vsa.Cbat_extraction.relativize_opt`. `relativize_opt`'s contract
  deliberately includes the plain-band smear arm — it is the TAG
  UNIVERSE's accessor (extract's address classification,
  `cbat_mem_key`), where "no real address lives in [2^61, 2^63)" is
  TRUE. The escape probe asked it about ARBITRARY INTEGERS, and gcc
  -O2's scratch checksum arithmetic (13/27 of spill_many's final
  values in `[2^61, 2^63)`) smeared into `sp_extents`. A plain
  in-band value now contributes nothing to `sp_extents`, to
  `frame_dims`, or to the values-served escape decision
  (`values_served = List.is_empty sp_extents`).
- **Simplification**: the old `singleton_i64 rel` special case is
  DELETED — min/max over a singleton is the same pair, so the StackOff
  arm's result is unchanged and the probe has one rule (denote →
  StackOff proof → hull extrema or the unbounded pair).
- **Untouched on purpose**: `singleton_stack_offset` (the SP-at-call /
  outgoing-store-address reader) keeps `relativize_opt` — it is the
  slot-correspondence question, not frame sizing; its plain arm is
  censused below (111 consults, all `_start`), and a wide hull is
  never a singleton, so the smear cannot manufacture a slot index.

## 2. The two hardenings (rules, not gates)

- **`build_frame_anchor` never loses bits** (`src/bil2llvm.ml`). The
  array count crosses the LLVM binding as a 32-bit unsigned (the stub
  computes `Int_val` → `unsigned`; LLVMArrayType's parameter), so a
  count ≥ 2^31 TRUNCATED SILENTLY while the anchor GEP kept the 64-bit
  index — the exact loss that turned spill_many's 4-EB request into a
  4,121,833,728-byte alloca. The switch's LLVM 19.1.7 bindings expose
  only `array_type : lltype -> int -> lltype` (no LLVMArrayType2), so
  the landed form is the loud arm: an absurd `n` is a Hike_diag
  warning (`frame: frame request %Ld bytes is absurd (array-count
  bound 2^31) — clamped; the producer's extents are wrong`) and the
  count/anchor stay consistent inside the representable frame. Never a
  silent truncation; the diagnostic names a wrong producer (with
  hardening (ii), unreachable on every sound input — 0 firings on the
  corpus, both lanes).
- **`frame_dims` degrades an absurd span** (`src/hike_stack_model.ml`).
  New `extent_absurd (l,h)`: an unordered (wrapped) pair, or a hull
  span at/above 2^31 (overflow-safe compare). An absurd extent — tag
  Range/Infinite/Mixed or a formed stack-value extent — is not folded
  as an extent: it joins the UNBOUNDED classification and the frame
  takes the bounded arm (the 64K window over the remaining facts),
  with a Hike_diag warning naming the sub and the span. This kills the
  int64-overflow collapse too (a full-range hull used to wrap `span`
  negative and could silently shrink `n`). 0 firings on the corpus.

## 3. The band-arm census (the owner's question) — the arm is LIVE; disposition: KEEP

The question: post-symbolic-base, how many ADDRESS-position
classifications legitimately reach `in_stack_segment`'s plain-band
degraded arm?

Mechanism (debug builds only; `#ifdef VSA_DEBUG` — erased from
production, proven: the final production install's bundle hash is
byte-identical with and without the census blocks,
`7ba492c8bf4bfbde`): counters + `at_exit` summary in
`cbat_vsa.ml`'s `is_stack_access` (stackoff vs band) and
`hike_vsa.ml`'s `singleton_stack_offset` (plain-band consults). The
installed-debug-plugin route is a dead end in this switch (the
vsa-debug plugin cmxs fails to dynlink: flambda leaves
`camlCbat_vsa__Pmakeblock_4917` undefined — the debug probes are
executables and self-contained, the plugin lane never had this path),
so the census ran through `dune exec --build-dir _build-debug
--profile vsa-debug zz_scratch_probe/audit02.exe -- <bin> ALL`: one
production `offsets_of_sub` per sub, every sub, every binary, both
lanes. The experiment on the shared plugin slot was fully reverted
(backup → restore → `record_provenance.sh`).

Result (37 binaries × 2 lanes, every binary identical):

| lane | StackOff classifications | band-arm classifications | slot-offset plain-band consults |
|---|---|---|---|
| -O0 | 4,513 | 111 | 111 |
| -O2 | 1,230 | 111 | 111 |

111 = 3 per binary, and all 3 are `_start`'s
`and $0xfffffffffffffff0,%rsp` — the SP-alignment idiom whose bitwise
result degrades the seeded StackOff to a plain hull INSIDE the band.
That is the exact "bitwise-mangled SP lane" the band was designed for,
and it fires on EVERY PIE binary (both lanes, 74/74 runs). Zero
data-dependent band entries: no corpus value from real sub arithmetic
ever classified through the band — the spill_many misfire class
(scratch integers in band) is gone from every DECISION site, because
integers no longer reach the band through the escape probe at all.

**Disposition: KEEP.** The arm's classification role is measured ALIVE
(not dead): it serves every binary's `_start`, its argument ("no real
x86-64 address lives in the band") is TRUE for the addresses it
re-tags, and deleting it would push `_start`'s aligned-SP derefs to
the untagged real-address lane — which claims they cannot alias the
frame, unsound for a value that IS the stack pointer's descendant.
Soundness over precision. The inventory is now explicit: the band
serves ADDRESS classification only, exactly one idiom on this corpus,
and the integer-side consumer (the escape probe) is deleted.

## 4. Gate table (battery `/home/tovpr/tm-battery/t14/`, tag `t14`)

| gate | result |
|---|---|
| provenance | tree=/home/tovpr/hike-t14, src_sha16 `3febf454ebbe17b6`, bundle `7ba492c8bf4bfbde` ✅ |
| dune runtest (units + referee) | PASS; clpequiv **2,861,148 / 0 mismatches** (both-raised 1300, the baseline) ✅ |
| -O0 emission | 37/37 rc=0 ✅ |
| -O0 structural asserts | check_allocas **185 passed / 0 failed** ✅ |
| -O0 semantics STRICT | **37 PASS / 0 FAIL** ✅ |
| -O0 opt-safety STRICT | **37 PASS / 0 FAIL** ✅ |
| -O2 emission | 37/37 rc=0 ✅ |
| -O2 structural asserts | check_allocas **185 passed / 0 failed** ✅ |
| -O2 semantics PINNED | **PIN-MOVED: IMPROVEMENT — spill_many** (31 PASS + the golden six; failing set = byte_copy, fizzbuzz_safe, jump_table_sw, union_overlap, va_arg_mixed, va_arg_vacopy — the pin **7 → 6**, no regression, no other movement). The golden list + AGENTS.md move in the MERGER's commit; this verdict records the flip ✅ |
| convergence report | exactly ONE row moved: spill_many o2model DIFF → **SAME** (134/4 insns, native 2388) ✅ |

Hardening firings on the corpus: **0** ("absurd" greps empty, both
lanes) — the backstops are silent on sound producers.

## 5. The emission delta (vs the merge-t10 reference)

- **-O0 lane: byte-identical 37/37.** The escape-extent rule changes
  nothing at -O0 (no -O0 sub had plain-band values feeding
  `note_escape` — the ticket's "why -O0 passes" analysis, now proven
  emission-side).
- **-O2 lane: exactly ONE binary — spill_many.** The entire IR delta
  is the frame geometry:
  - pre-fix (merge-t10): `%frame = alloca [4121833728 x i8]`, anchor
    index 4,007,929,975,690,637,560 (the 4-EB span, count truncated by
    the unsigned binding, anchor 64-bit);
  - post-fix: **`%frame = alloca [240 x i8]`, anchor 232 —
    byte-identical to the merge-t1 `emit-o2-real` pre-T4 reference
    shape cited in the ticket** (verified: lines 13-14 match).
  spill_many's -O0 IR is unchanged and its -O0 semantics keep passing.

## 6. The exposure-class sweep (calls after heavy 64-bit arithmetic)

The same misfire exposed any -O2 binary whose param registers hold
scratch 64-bit arithmetic at a call block. The mechanical proof the
class is clean: the -O2 emission delta vs merge-t10 is exactly
{spill_many} — no other binary's escape/frames/values-served decision
consumed a fake extent — and the pinned gate + convergence show zero
other movement. The class rows, re-checked against merge-t10's
conv.log (all unchanged): deep_chain 323/4 SAME, ptr_chain 87/4 SAME,
many_args 58/4 SAME, list 310/264 SAME, jump_table_sw 623/6 (the
recorded DIFF, unchanged), fptr_table 77/72 SAME, fn_table_disp
279/270 SAME, nested_calls 75/4 SAME, mixed_fp_int 68/4 SAME,
alloca_vla 65/4 SAME. The census agrees from the producer side: zero
data-dependent band entries on either lane.

## 7. Notes for the record

- The rename `as_stack` → `stack_offsets` carries T3's accessor into
  the rule's vocabulary; `cbat_walk.ml`'s `stack_anchor` (the T3
  anchored-cell proof) is its only other consumer and is unaffected.
- The census instrumentation is COMMITTED (debug-profile-only, two
  `#ifdef VSA_DEBUG` blocks + at_exit summaries) so the census is
  reproducible: rebuild the vsa-debug probe and re-run the audit02
  sweep. Production builds erase it — proven by the identical bundle
  hash across the census edit.
- The debug-PLUGIN dynlink wall (flambda `Pmakeblock` hole) is
  pre-existing and unrelated to T14; the vsa-debug EXECUTABLES are the
  working debug lane. Worth a ticket only if an installed-debug-plugin
  need ever arises.
- sp_reload's channel-2 pin (the reloaded-pointer derefs) is untouched
  — its extents are genuine StackOff cells and its IR is byte-identical.
