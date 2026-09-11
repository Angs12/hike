# test-audit verdict — "test the project, not BAP" sweep

Lane: `tm/test-audit` (worktree `/home/tovpr/hike-audit`), 2026-09-11.
Directive (owner, binding, spec-v2): **"DO TEST BAP LIBRARY LOGIC!! THAT IS
WRONG! Do not test BAP itself — only test logic of the project. BAP is not
the project!"** Every check classified against the deletion test: *if hike's
code were deleted but BAP stayed, could this check still pass?* Yes →
framework → delete.

## The scope ruling (load-bearing)

**"BAP" = the framework libraries** (`Bap.Std`, `Bap_knowledge.Knowledge`,
`bap-main`, `bap-future`, `Graphlib`, `Llvm`, BIR term/builder machinery).
**The vendored analysis (`src/cbat_vsa/`) is PROJECT code**: the repo owns,
maintains and modifies it (the landmark-directed widening, the NEQ/EQ jcc
decoder rows, div-by-{0} word semantics, the R2-1 meet clamp, the whole
backward-refinement walk are hike's contributions, not upstream CBAT and
not BAP). Checks over `Clp`/`FinSet`/`Cbat_word`/`Ws`/`AI`/`Mem`, the
fixpoint, the extraction, and the refinement seams assert the project's
analysis logic and are PROJECT-LOGIC. Hike-repo modules (`Hike.Vsa`,
`Hike.Stack_model`, `Hike.Stack_to_locals`, `Hike.Bil2llvm`, `Hike.Dce`,
`Hike.Jump`, `Hike.Kb`, `Hike.Abi`, `Hike.copy_reloc_slots`) are trivially
project.

## Enumeration and classification

Authoritative counts are runtime `ok:` lines (`dune runtest --force`).
621 at baseline → **620 checks after the sweep** (the delta is the one
deletion, below). Every one of the 620 survivors transitively calls a
module that lives in this repo; none survives the deletion test as
framework.

| file (module) | checks | class | ruling |
|---|---|---|---|
| test_domains.ml `run_base` (CLP/FS/ML/WO/W-diff) | 63 | PROJECT | the vendored domain's construction/lattice/diff contracts; hike's own modifications (wrap handling, cardn at w+1 bits) are what these pin |
| test_domains.ml `run_policy` (P5/A1/D3/D1/D2/EX) | 37 | PROJECT | totality + soundness contracts of the vendored ops (no-raise rows, widen_join soundness — the landmark lane's surface) |
| test_domains.ml `run_agreement` (O4c/opadd) | 37 | PROJECT | Int64-vs-Big agreement + the Mem interval-map op_add contract |
| test_domains.ml `run_shifts` (A/D5/D7-shift/E2eC) | 30 | PROJECT | the CLP shift semantics (overshift={0}, coercion) hike defined |
| test_domains.ml `run_overlap` | 19 | PROJECT | overlap/meet/round-trip properties (hike's representation invariants) |
| test_seed.ml (T1–T4, S1–S15a/b) | 20 | PROJECT | hike's trace-exact cell meets + the seed collector's rule rows (EQ/NEQ/SLT/flip/producer/cast) |
| test_vsa.ml (D4, E3, D6, D6b, E6, T2/T3, T4, F1-fold, C1, P21–P23, D7, E2eH/C/D, P3, L2b) | 85 | PROJECT | guard refinement (incl. hike's NEQ row D4-6), width-mismatch totality, call abstraction, extraction seeding, soundness pins (E2eD-7/8 re-derived), 1-bit cardn fixes |
| test_backward.ml (L3a/L3c1–5/S/B/L-B/L-D2/L-D6/E1/R2/M5) | 55 | PROJECT | the backward walk, producer subtraction, flag-state recovery, jcc decoder rows, landmark loops — the trace-partitioning design's pins |
| test_regression.ml `run_creg` (C1/C3/C4a/C4b/R11) | 9 | PROJECT | the OR-mask rewrite widths, frame-survives-call, region merge/convertibility tags |
| test_regression.ml `run_remediation` (A1/A4a-c) | 5 | PROJECT | OR-mask widths u8/u32, neighbor-cell survival |
| test_regression.ml `run_regions` (R12-1…9b) | 9 | PROJECT | `region_bytes` geometry properties, split_plan coverage, sweep partition + id determinism |
| test_regression.ml `run_t4_resolution` | 4 | PROJECT | `resolve_target`'s four classes (singleton/multi/foreign/TOP) |
| test_regression.ml `run_copy_reloc` | 8 | PROJECT | `copy_reloc_slots` mirror rule (kept/filtered classes) |
| test_regression.ml `run_fp_gpr` (S2/S2b/S3/S4) | 4 | PROJECT | stack-ness is the tag, never the register name (ADR 0008) |
| test_model.ml (PR-A/B/C/D/E, the coverage lane's 48) | 48 | PROJECT | producer record end-to-end, frame-geometry arms, STL fission/slot/ABI-visible arms, emitter alloca shapes, Abi facts, KB domain |
| test_properties.ml `run_soundness` (R10b/R5/R7) | 5 | PROJECT | sampled logand/meet soundness vs independent references; fixpoint stabilization |
| test_properties.ml `run_roundtrip` (W1) | 4 | PROJECT | of_list containment/exactness properties |
| test_properties.ml `run_landmarks` (F1/F1-NEQ/FT/B1–B4/VSK/F2a/F2c) | 33 | PROJECT | landmark acquisition/consumption, budget soundness, walk/memo pins |
| test_properties.ml `run_chains` (T01) | 4 | PROJECT | accumulated-cond partition (when-chain), identity transfer |
| test_dce.ml (D0–D5) | 6 | PROJECT | the DCE lane's keep rules, epilogue rewrite, region-mem two-tier rule, intrinsic passthrough |
| test_jump.ml (T13) | 42 | PROJECT | the jump compiler's flag-effects table rows + residual/identity classes |
| test_bil2llvm.ml (FP-TABLE/POISON/SP-RESTORE/CAST/GOLDEN/FP-GPR/T4-PROM/THUNK/PTR/T10) | 93 | PROJECT | the 26-row FP table (map + per-row emission), the poison/undef diagnostic contracts, the promotion/thunk/pointer-call emission, the T10 BIR rewrite |
| **test_regression.ml — the M3 printf stub** | **1** | **FRAMEWORK-shaped: asserts nothing** | **DELETED** (see below) |
| | **620** | | |

## The deletion (1)

`test_cbat/test_regression.ml`: the block

```ocaml
(  Printf.printf "ok: property M3 fused_join invariants (skipped due to API change)\n";
  ())
```

inside `run_regions`'s body. It is not a check — it prints `ok:` with no
assertion (a survivor of the API change that predates the honest-gate
lane's sweep of the 38 stubbed sites; it prints instead of calling
`check`, so the failure counter never sees it). This is the same
dishonesty class the honest-gate lane deleted, and it fails the audit
principle trivially: it asserts nothing of hike OR BAP. Its stated
concern (the fused map-lattice join invariants) is pinned by the ML1–ML7
checks in test_domains.ml. An orphaned-fixture sweep found nothing to
remove: no fixture builder lost its last caller (checked against the
fixture-lib rule).

Count delta: **621 → 620** runtime oks; the other 620 ok lines are
byte-identical between the same-tree baseline run and the post-deletion
run (diff verified — the only differing line is the deleted stub).

## Borderline calls and rulings

1. **test_model.ml §E, the KB pins (PR-E2)** — KEPT. The task flagged
   them as Knowledge-machinery-smelling. Resolved by reading the source:
   `map_order`, `map_join`, `info_join`, `info_of_sub` are HIKE's own
   functions (`src/hike_kb.ml` 33–74, 100–103); BAP's Knowledge only
   HOSTS the domain (`KB.Domain.define ~join:map_join ~order:map_order`).
   The checks call the pure functions directly and pin hike's semantics:
   extension order, subset-join-takes-bigger, disjoint union, and the
   conflict REFUSAL — the refusal is hike policy ("two different VSA
   results … refusing to drop either", the registered conflict printer).
   `info_of_sub` absence = the empty record is hike's identity-record
   contract. Delete hike's code and these fail to compile — project.
2. **test_vsa.ml E6-1/E6-2 (not_implemented channel)** — KEPT. Pins
   hike's one-channel diagnostic decision (the vendored lib's eprintf
   duplicate is deleted; Event.Log only). BAP's Event.Log is the
   sanctioned channel; the asserted fact is hike's channel choice, and a
   re-added eprintf would fail these.
3. **test_domains.ml P5's `Event.stream` observation** — KEPT. BAP
   machinery (a stream observer) used to assert a hike fact (the warning
   line names the component) — the explicit keep rule.
4. **test_model.ml PR-A5's kind "round-trip through the stamp"** — KEPT.
   `stamp_def_kinds`/`def_kind` are hike's T10 stamp functions; the pin
   asserts hike's contract (the VLA kind rides the def's value), not a
   BAP attribute round-trip. Same ruling for T10-PROMOTE's "stamped kind
   survives the rhs rewrite".
5. **test_model.ml PR-E1's `Theory.Target.matches` conjunct** — KEPT as
   part of a hike check (the x86_64 reification of the SP through
   hike's `of_target_opt`); the BAP conjunct alone is not the assertion.
6. **test_jump.ml "CFG unchanged"** — KEPT: hike's pass contract (the
   jump compiler rewrites conds only; targets and block count are its
   obligation), asserted through BAP's term readers.
7. **Domain lattice-law checks (CLP9/10/13/14/17, FS4–FS6, ML1–ML7)** —
   KEPT: algebraic laws OF THE VENDORED DOMAIN, which is project code
   (scope ruling above); they are the regression guards for hike's own
   domain modifications (the R2-1 meet clamp could break commutativity;
   CLP9 would catch it).
8. **Redundancy observed, NOT deleted (out of scope — these are
   project-logic duplicates, not framework tests):** test_vsa T3-1 ==
   T3-2 (byte-identical guard + assertion); test_domains EX1 == EX1b
   (identical assertion); test_properties F2a "widen_join sound 1..5"
   (the same three subset assertions repeated); test_regression A1 runs
   the fixpoint and ignores the solution (its main assertion died with
   the escape machinery; only the non-vacuous pre-state pin remains).
   Recorded for the owner; a dedup is a deliberate lane, never a rider.
9. **`precision_probe.ml` / `corpus_watch.ml`** — not `dune runtest`
   checks (manual dune-exec drivers over real binaries); scanned, they
   assert hike analysis behavior on corpus binaries — project; out of
   the classification table.

## Concurrent-work note

Zero edits to `test_cbat/test_model.ml` — the written-slot demotion
checks (PR-A4) another agent is fixing on a different branch are
untouched; the only deletion is in `test_regression.ml`.

## Gates (this lane's final tree)

| gate | result |
|---|---|
| `dune build` (default profile) | rc=0 ✅ |
| `dune runtest --force` | rc=0, `ALL CBAT TESTS PASSED`, **620 ok / 0 FAIL** (baseline 621 − the stub) ✅ |
| referee (`clpequiv` stanza) | **2,861,148 checks / 0 mismatches** (both-raised 1300, unchanged) ✅ |
| ok-line diff vs same-tree baseline | byte-identical minus the one deleted stub line ✅ |
| `dune install` / `bap` | NOT run per lane constraint (shared plugin slot held by another agent) — no src/ change, so the plugin is bit-identical by construction |

## Conclusion

The sweep's finding: after the honest-gate lane (2026-09-07) deleted the
38 stubbed sites and T13 moved the jcc coverage into table pins, the
suite contains exactly ONE framework-shaped remnant — the M3 printf
stub — now deleted. All 620 surviving checks assert hike's logic: the
flag-effects table (T13, FP-TABLE), the rewrite rules (STL, DCE, jump
compiler), the promotion's correspondence (T4/T10 pins), the storage
decisions (regions, layout, split_plan), the diagnostics contracts
(poison, undef-read, absurd-frame, channel pins), and the producer
record's facts (A-lane). The directive is satisfied not by mass deletion
but by verification: nothing left tests BAP.
