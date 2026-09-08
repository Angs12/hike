# SP-only stack semantics: fp (RBP) becomes an ordinary callee-saved GPR

Status: **ready-for-agent** (grilling-settled 2026-09-08, four rounds; ADR 0008 is the
decision record). Base tree: current main (post cleanup-9 @ the 2026-09-08 record).

## Problem Statement

The tree grants the frame-pointer register stack semantics BY NAME in a belt of
syntactic helpers rooted at `Abi.is_stack_reg = is_sp || is_fp`, while the VSA's
tagging path is already value-based (the entry anchor seeds SP only; RBP's stack-ness
comes from its computed frame term; the heap-RBP case is fixture-pinned UNtagged —
P23-1/P23-2, `mk_gpr_rbp_sub`). At -O2 (omit-frame-pointer), RBP is an ordinary GPR
holding heap/static pointers, being read without a definition, and being spilled
through like any other register. The by-name belt therefore:

1. **Degrades whole subs by name** (a precision bug): an untagged heap-RBP store
   fires `has_unbounded_access` (via `exp_contains_sp`'s fp disjunct) and
   `sp_escaped`'s seed includes RBP unconditionally — either forces the whole-sub
   model-frame fallback (`split_plan` returns `[]`).
2. **Invents emitter values** (a soundness bug on the -O2 class): `build_entry_block`
   binds `fp := anchor−8` at entry for every non-precise sub — a sub that READS RBP
   without defining it gets the model frame instead of the true incoming value (a
   heap pointer read from the caller's RBP).
3. **Mislabels cast widths by name** (an -O2 correctness bug): `u32_slots_of_sub`
   treats any 32-bit store at `[RBP ± w]` as a spill slot (`Abi.is_fp`), so a
   GPR-RBP 32-bit store picks the wrong `sitofp` source width.

And the entire RBP-as-GPR class is INVISIBLE to the battery: `compile_corpus.sh` is
-O0-only (every prologue makes RBP sp-derived), so no gate would catch a regression
in this lane and today's -O2 behavior is unmeasured.

## Solution (the shared understanding, per ADR 0008)

**SP is the only register granted stack semantics by fiat.** RBP/fp is an ordinary
callee-saved GPR whose stack-ness — like any register's — is PROVEN, never assumed.
The three proof routes:

| Route | Home | Consumes |
|---|---|---|
| Frame term (VSA tagging, channel 1) | `apply_frame_def_list` + `is_seed` — UNCHANGED (already value-based) | the tag itself |
| SP-seeded syntactic closure (escape ONLY) | `sp_escaped`'s derived closure, re-seeded `{SP}` | escape analysis |
| The tag's own offset span | `vsa_kind` = `Range (lo,hi)` — a SINGLETON span is a proven constant offset | directness, fission binding |

**No per-def fact is added.** An earlier draft of this spec proposed a `base_const`
(base var × constant offset) field; it is REJECTED by the generality argument: the VSA
already proves the offset, and the proof travels in the tag. A per-def
`base_const` would be an ad-hoc re-derivation of what `vsa_kind` already says —
and less general (it would need a base var NAME, while the tag works for any
provable base, including `R12`-as-frame-pointer). The three consumers reduce to
the tag: directness = "the proven offset is constant" (singleton `Range`);
fission binding = the base is the frame/region, no register name needed.

**Stack-ness of an ACCESS = the tag alone.** Both syntactic disjuncts of
`has_unbounded_access`'s untagged arm drop (sp and fp). Untagged accesses emit through
the generic real-address lane. Accepted risk (ADR 0008): the rsp-term-lost edge (an
unproven sp-mentioning access could share a physical cell with a converted region
member → split storage) — principle-#2-consistent (the disjunct was a
refusal-to-refine gate), the Unbounded-TAG fallback arm remains, byte-identity and
semantic gates are the empirical guard.

**The emitter never invents register values** (`fp_anchor` deleted → undef+warn lane);
**spill detection DELETED** (the no-gates ruling: the cast's source width IS the
operand value's own LLVM type — a lifter `31:0` extract builds i32, a `:u64` load
builds i64; no register name, no tag test, no width test); **degraded extents come from
the tags** (a tagged-unconverted access needs frame coverage; an untagged one never
touches %frame — growth stays the syntactic MINUS-on-sp walk).

**The ABI absorbs the frame-pointer concept** (the minimality directive carried to the
field): `Abi.fp`/`is_fp`/`is_stack_reg`, `Hike_stack_model.fp_of`/`is_sp_or_fp`,
`Convutils.fp` all deleted; RBP moves into `callee_saved` — the preserved set
`sp :: callee_saved` is provably the same registers as before. `Abi.sp` stays as the
one granted fact.

**Deferred to its own lane (recorded in ADR 0008):** channel-2 provenance (dual-lane
bits — per-cell content-provenance bit in Mem + per-var provenance set in AI, channel 2
seeding iff provenance-clean AND bounded in the window; the environment-conditional
soundness argument; `anchored_entry`'s RBP={0} seed deleted; fixtures earn prologues
via the `mk_rsp_prologue_sub` pattern). This lane does NOT touch the seeding rule.

## Inventory (what changes, per module — line refs live in the grill record; this
spec names functions only so it doesn't rot)

**VSA core (`src/cbat_vsa/`):**
- `prove_nonneg`'s `stack_anchor` (`cbat_walk.ml:171`): `is_stack_reg` (name) →
  frame-term-based ("≥1 free var AND all free vars of the address have frame terms in
  the current state"); a constant address is NOT anchored — an empty free-vars set must
  REFUSE, never pass vacuously (the 18a368f privacy-proof fix).
- `preserved_of_sub` (`cbat_vsa.ml:86-89`): unchanged behavior — becomes
  `sp :: Abi.callee_saved` (RBP arrives via the list; same register set).
- Extraction (`Cbat_extraction.extract`): the `base_const` fact was CANCELLED (spec
  §Solution) — the tag IS the proof; no export was coded.
- Tagging path, `constrain_cell`, `frame_add_rsp`, call abstraction frame-keeping,
  VLA detection: UNCHANGED (already sp-only/value-based).

**Stack model (`src/hike_stack_model.ml`):**
- `sp_escaped` → `frame_escapes`: derived-set closure re-seeded `{SP}` (fp NOT seeded;
  terms under-approximate, and missing an alias is the unsound direction). Var-based
  closure (EVER-held counts) stays — the conservatism is the soundness mechanism.
  Escape SURVIVED BY MEASUREMENT (T4): deleting it lost 5 binaries (the access through
  an escaped frame pointer is UNTAGGABLE IN PRINCIPLE — TOP in the callee's sub; the
  caller is the only sub holding the fact).
- `frame_addr_alias`: TAG-GATED — an UNTAGGED read through a materialized frame
  address vetoes; tagged ones are proven (replaces the RBP-by-name exclusion which had
  silently exempted every -O0 prologue).
- `has_unbounded_access` SP arm: untagged-only (the VLA class needs it); a tagged
  access's fallback is decided by its own tag.
- `is_direct_const_addr`: name test → tag span (a SINGLETON `Range` = a proven constant
  offset).
- `degraded_geometry`: TAG-DRIVEN — extents from `info.offsets` spans; Unbounded →
  whole-frame flag; growth keeps the MINUS-on-sp walk. Signature `(sub, info)`.
- `fp_of`/`is_sp_or_fp`: DELETED.

**Stack-to-locals (`src/hike_stack_to_locals.ml`):**
- `base_exp_of`: tag-regime — any Var base; callers are tagged convertible members
  only (no register-name test).

**Emitter (`src/bil2llvm*.ml`):**
- `build_entry_block`: `fp := anchor−8` binding DELETED → never-defined RBP reads
  take the undef-read + `Hike_diag.warn` lane (the RBX treatment).
- `collect_sub_data`'s SP/FP lane-keeping: becomes sp ∪ callee_saved (RBP now a
  callee-saved GPR whose defs must thread phis at -O2).
- `compute_sub_sig`: the fp test is absorbed by `is_callee_saved` (same filter
  result).
- `is_plt_trampoline` (`bil2llvm_mem.ml`): sp-only exclusion.
- `u32_slots_of_sub`/`cast_source_width`/`has_32bit_extract`/`x0_temp_name`
  (`bil2llvm_calls.ml`): ALL DELETED (the no-gates ruling, T6). NEW: the STATIC
  model-interface table `fp_op_inputs` — the mapped intrinsic name IS the interface
  fact; `create_native_fp_call` resolves operands from the block's `intrinsic:xN`
  temps (never a signature-table fallback that could substitute a register lane).

**ABI (`src/hike_abi/hike_abi.ml`):**
- `fp` field, `is_fp`, `is_stack_reg` DELETED; `callee_saved` gains RBP
  ([RBX;RBP;R12..R15]); `of_target` stops reading `frame_pointer`; `is_sp` stays.
- The ticket greps for every `callee_saved`/`is_callee_saved` consumer whose
  behavior could change when RBP joins the list (compute_sub_sig, preserved_of_sub,
  collect_sub_data, DCE keep policy if any) and proves each unaffected or adjusts.

**Fixtures/tests (`test_cbat/`):** `anchored_entry`'s RBP={0} word seed STAYS this
lane (the provenance lane owns its deletion); RBP-stack-ness fixtures that lean on
the seed for CELL KEYS keep working (they test the words lane, not stack-ness); the
NEW reproducer fixtures earn fp-ness via explicit prologue defs. Probes:
`precision_probe.ml:290-295`'s `is_stack_addr` ("Stack iff the name is RSP/RBP")
switches to the tag.

## Gates

- **-O0 corpus (32 bins): IR byte-identity 32/32** vs a pre-change control emission
  (the T06 commit: 32/32 vs red3-o0, with the one SOLO delta the SFLOAT lane — the
  deleted trunc+sitofp-i32 becomes sitofp at the operand's own type, semantically
  proven 32/32 at both -O0 and opt -O2).
- **-O0 semantics**: full suite green (32/0 at -O0 and opt -O2 on T06).
- **-O2 corpus (NEW, 32 bins — same sources, -O2 -fno-stack-protector, PIE-only,
  second directory):** `compile_corpus.sh` builds `<out>-o2` (or a lone `-o2` dir);
  semantic harness (native-vs-lifted) + check_allocas; no emission baseline exists —
  snapshotting today's buggy -O2 output would pin the bug.
- **Unit suite**: honest count updated; new fixtures land RED first (T1), flip green
  with the fix.
- **Full battery** per the AGENTS.md ritual (`dune runtest`, instrumentation blocker
  both profiles, probes, unmapped-intrinsic grep, provenance record after install).

## Ticket map (dependency order)

- **T1 — Reproducers land RED.** Model-level: heap-RBP sub (the `mk_gpr_rbp_sub`
  shape) asserting false frame-escape/unbounded-fallback today; -O2 emission
  reproducer (fp_anchor invented value; cast-width). Pin the model-level fallout
  with fixtures asserting the POST-fix truth (they stay red until T4/T5).
- **T2 — VSA: `prove_nonneg` frame-term anchor.** The one in-VSA name site. -O0
  identity expected (RBP carries a term there) — the corpus gate arbitrates.
- **T3 — (CANCELLED)** the `base_const` export — superseded by the no-gates ruling:
  the tag IS the proof (see §Solution and ADR 0008's base_const cancellation).
- **T4 — Model rules.** SP-seeded escape closure (`frame_escapes`) + the
  tag-gated `frame_addr_alias`; `has_unbounded_access`'s SP-only untagged arm;
  `degraded_geometry` tag-extents/sp-growth. T1 model fixtures flip green.
- **T5 — Emitter.** `fp_anchor` deletion; `collect_sub_data` sp∪callee_saved
  lane-keeping; `compute_sub_sig` absorption; `is_plt_trampoline` sp-only;
  `u32_slots_of_sub` DELETED. T1 emission reproducers flip green.
- **T6 — ABI absorption + the spill deletion.** fp field/predicates deleted, RBP
  into callee_saved, the `callee_saved`-consumer grep with proofs; the spill
  apparatus (`u32_slots_of_sub`, `cast_source_width`, `has_32bit_extract`,
  `x0_temp_name`) DELETED and replaced by the static `fp_op_inputs` interface
  table; the by-construction cast-width pins land.
- **T7 — -O2 corpus build + gates.** `compile_corpus.sh` grows the -O2 lane (the
  `<out>-o2` second directory); run_corpus/check_allocas/semantics over it.
- **T8 — Docs.** ADR 0008 references (CONTEXT.md entries landed with this spec;
  AGENTS.md refresh at lane end per the non-negotiable directive).

Each ticket: full battery at its tip; T06 is the one deliberate-IR-delta ticket
(the SFLOAT lane), semantically proven at both levels.
