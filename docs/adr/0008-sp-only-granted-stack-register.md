# ADR 0008: SP is the only granted stack register; fp is an ordinary callee-saved GPR

Date: 2026-09-08 · Status: accepted · Supersedes: ADR-0001's SP-only seeding clause (carried
forward); supersedes the cleanup-9 ticket 07's "rescope (sp,fp)→Abi.t to nothing" premise
(`.scratch/cleanup-9/07-stack-model.md` §"rescoped to nothing")

## Context

The tree treated the frame-pointer register as a stack register by NAME in a belt of
syntactic helpers rooted at `Abi.is_stack_reg = is_sp || is_fp`: the model's
`is_sp_or_fp`/`exp_contains_sp` (escape seeding, frame aliasing, directness,
unbounded-access detection, degraded geometry), the emitter's `fp := anchor−8` entry
binding, `u32_slots_of_sub`'s RBP-spill detection, and one in-VSA name site
(`prove_nonneg`'s `stack_anchor`). At -O2 (omit-frame-pointer), RBP is an ordinary GPR —
holding heap/static pointers, being read without a def, being spilled through like any
other register. The VSA's tagging path was already value-based (the entry anchor seeds
sp only, `seed_frame`; RBP's stack-ness comes from its computed frame term; the
heap-RBP class is fixture-pinned UNtagged, P23-1/P23-2), so the by-name belt could not
manufacture false TAGS — but it degraded whole subs by name (an untagged heap-RBP
store forced the whole-sub model-frame fallback via `has_unbounded_access` and
`sp_escaped`'s seed) and the emitter INVENTED an entry value for never-defined RBP reads
(`anchor−8`, the -O2 GPR-RBP unsound-emission class).

## Decision

**SP is the only register granted stack semantics by fiat.** fp/RBP is an ordinary
callee-saved GPR whose stack-ness — like any register's — is PROVEN, never assumed:

- **Frame term** (the VSA's tagging channel 1): the value-computed route; at -O0 the
  prologue's `RBP := RSP` copy gives RBP its term, at -O2 heap-RBP never gets one.
- **SP-seeded syntactic closure** (escape analysis only): `sp_escaped`'s derived-set
  closure keeps its conservative VAR-based shape, re-seeded `{SP}` — the
  over-approximation is the rule's SOUNDNESS mechanism (`RAX := RSP − mem[x]` is
  syntactically derived, value-unproven, a real frame address at runtime). RBP joins
  via its prologue def at -O0 (byte-identical closure), never at -O2 (the false-escape
  precision win).
- **Per-def `base_const` fact** (directness/fission-binding/spill-gating): one new
  per-def field in `vsa_info` — the address's base var and its constant frame offset
  (its frame term when fconst-only); None when no Var base or the term carries fvars.

**Stack-ness of an ACCESS = the `vsa_info` tag alone** — under the 100% invariant the
tag is the only carrier, so BOTH syntactic disjuncts of `has_unbounded_access`'s
untagged arm drop (sp and fp). Untagged accesses emit through the generic real-address
lane against their true runtime values (sound). **Accepted risk, recorded:** an
unproven sp-mentioning access (the rsp-term-lost edge — a weird `RSP := RAX` rebind
that drops RSP's frame term) could at runtime address a cell a converted region member
also addresses; the untagged access then writes real stack while the member writes the
alloca — the split-storage (write-closed violation) class. Dropping the sp disjunct is
principle-#2-consistent (it was a conservative refusal-to-refine gate; the
Unbounded-TAG fallback arm REMAINS — a tagged-Unbounded access still degrades the
sub). The byte-identity and semantic gates are the empirical guard.

**The emitter never invents register values.** The `fp := anchor−8` entry binding is
deleted; never-defined RBP reads fall into the existing undef-read + warn lane (the
same treatment as RBX). Lane-keeping and signature computation keep their ABI facts:
fp is never a param register, and GPR-RBP values must thread phis at -O2 (the
sp-lane-keeping test becomes sp ∪ callee-saved).

**Spill-slot detection (`u32_slots_of_sub`) tag-gates.** A 32-bit store is a spill slot
iff it carries a stack tag (the VSA proved the cell frame-resident) — value-true, and
it fixes the RBP-name asymmetry (RSP-based 32-bit spills were never detected). This is
the lane's one deliberate -O0 identity risk (an RSP-based tagged 32-bit store could
flip a sitofp width i64→i32), gated by measurement.

**Degraded geometry is tag-driven for extents, sp-driven for growth.** The fallback
%frame is sized from the tags' own offsets/spans (a tagged-unconverted access needs
frame coverage; an untagged one never touches %frame — sp-only syntactic extents would
UNDERsize the frame for -O0 RBP-tagged accesses, unsound); frame growth stays the
syntactic MINUS-on-sp walk (the granted fact; catches rsp-sub prologues).

**The ABI absorbs the frame-pointer concept.** The `fp` field, `Abi.is_fp`,
`Abi.is_stack_reg`, `Hike_stack_model.fp_of`/`is_sp_or_fp`, and `Convutils.fp` are
DELETED; RBP moves into `callee_saved` (`[RBX;RBP;R12..R15]`, the SysV truth) — the
preserved set `sp :: callee_saved` is provably the same registers as before;
`Abi.of_target` stops reading the target's `frame_pointer`. `Abi.is_sp` stays as the
ONE granted fact. Minimality carried to the field: no predicate survives without a
consumer, and no register fact exists that the analysis does not prove or the ABI does
not need.

## Considered options

- **Minimal-predicate variant** (keep `Abi.fp` inert / stop calling the predicates):
  rejected — dead predicates rot, and the collision with spill detection showed every
  name-based hook eventually finds a consumer.
- **Per-def VSA facts for escape too:** rejected — the closure's conservatism IS the
  soundness mechanism; value-facts would need unknown⇒escape polarity, collapsing
  precision (TOPs at arg registers are everywhere).
- **Closure ∪ facts for escape:** rejected — the closure already subsumes the frame
  terms; strictly more conservative for zero soundness gain.
- **Keep the untagged sp disjunct (tags + sp-syntactic):** rejected — it is a
  conservative refusal-to-refine gate (principle #2 bans the class); the edge it
  covered is accepted above.

## Consequences

- **`preserved_of_sub` = `sp :: callee_saved`** — RBP remains preserved across calls
  (callee-saved ABI fact, not a frame-pointer grant); `test_vsa.ml`'s T4-10 pin
  compiles unchanged.
- **`compute_sub_sig`'s fp test is absorbed by `is_callee_saved`** (same filter
  result: fp is never a sub param); `is_plt_trampoline` excludes sp only (a stub
  genuinely using RBP honestly isn't a pure trampoline).
- **Channel-2 conflation, DEFERRED to its own lane (this decision):** the
  frame-residency proof's neighborhood-subset channel seeds any bounded value in
  (−64KiB, +64KiB) as frame-resident — a genuine low absolute address is conflated
  with a caller-frame offset. It is sound CONDITIONALLY on the environment (Linux
  `mmap_min_addr` ≥ 64KiB, PIE's high addresses: a value in the window cannot be a
  mapped absolute address, so on any NON-CRASHING run it is frame-relative; the
  conflation is observable only on crash paths, which the semantic harness never
  compares). The sound mechanism (dual-lane provenance bits: a per-cell
  content-provenance bit in Mem set when a store's data is frame-derived, a per-var
  provenance set in AI assigned at Load from a clean cell, channel 2 seeding iff
  provenance-clean AND bounded in the window) is a follow-up lane with its own ADR;
  `test_common.ml`'s `anchored_entry` RBP={0} seed (which MANUFACTURES the conflation
  in fixtures) goes with it, and fixtures earn fp-ness via explicit
  `RBP := RSP` prologue defs (the `mk_rsp_prologue_sub` pattern).
- **The directness rule gains coverage:** with `base_const`, a hand-assembly
  R12-as-frame-pointer region member (a base that is provably sp-derived but is not
  RBP) now converts — the by-name rule never could.
- **`prove_nonneg`'s anchor becomes frame-term-based** ("all free vars of the address
  have frame terms in the current state") — preserves the -O0 refinement exactly
  (RBP has a term there) and drops heap-RBP correctly.
- **A permanent -O2 corpus joins the battery** (`compile_corpus.sh` builds both): the
  RBP-as-GPR class is otherwise invisible to every gate, and -O0 IR byte-identity
  (32/32) is the -O0 gate; -O2 is gated on the semantic harness + check_allocas with
  tag-kind before/after as measurement.
- Future SP work goes through `Abi.sp` (the target's stack_pointer) only; future
  frame-pointer work goes through the frame term or the closure — never a register
  NAME. ADR-0001's "SP-only, `RBP` is a GPR" clause is hereby carried forward from
  seeding into the whole pipeline.
