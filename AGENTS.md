# AGENTS.md — hike

BAP (OCaml/dune) plugin that lifts x86-64 ELF binaries to LLVM IR (the `hike-convlir`
pass), backed by a vendored port of CBAT's value-set analysis (`src/cbat_vsa/`).
There is no README; `docs/*.md` and `.slim/deepwork/*.md` (gitignored but searchable
via `.ignore`) are the design record.  The single source of truth for every
workstream — the stack-model endgame (Phase 1 dynamic allocas, Phase 2
region-split allocas, Phase 3 statics), the Option-B correctness fixes, and the
O-series performance work (O1 done, O2-O4 approved-pending, O5-O7 planned) with
the validation gates and the proposed execution order — is `docs/hike-full-plan.md`.

## Design principles (NON-NEGOTIABLE)

1. **CONCISE, SIMPLE, COMPLETE, ROBUST.**  The analysis must work completely on MOST
   binaries — arbitrary lifted x86-64, not just the corpus — and every change must
   keep the full chain green: `dune runtest`, the precision probe over `/tmp/corpus`,
   the corpus run (0 surviving diagnostics), `check_allocas.sh`, and the 8/8 semantic
   harness.
2. **NO GATES.**  No conservative refusal-to-refine conditions (no single-def gate, no
   cell-address gate, no refineable gates in the backward lane, no non-negativity
   gates, no NOT singleton gates).  The trace partition (taken/fallthrough views) +
   the producer subtraction + the trace-exact cell meets are the ONLY soundness
   mechanism.
3. **NO FALLBACKS.**  Every guard shape, producer op, cast kind, unop, and structural
   form has a complete rule.  A rule never silently produces BOTTOM on a live path
   (bottom claims the path is dead — unsound when the operand merely widened; the
   `Clp.sdiv` of an unbounded operand must be TOP, not the collapsed `{0}`).  The
   identity (top / "no constraint") is the sound fallback, never a stop, never
   bottom.
4. **Vocabulary:** a **rule** derives the **constraints** the operands must satisfy
   given the result constraint (never "row", never "pre-image").  Names say what
   they produce: `operand_constraints`, `def_constraints`, `edge_constraints`,
   `edge_views_of`, `constrain_cell_on_trace` (see `docs/trace-partitioning-plan.md`
   §9 for the full map).
5. **Soundness over precision, always.**  A sound over-approximation that loses
   precision is acceptable; an unsound narrowing (excluding a reachable value) is a
   bug — it is the array_local-class semantic failure.  The 8/8 semantic harness is
   the oracle.
6. **Debug instrumentation lives in the debug build ONLY.**  The `vsa-debug` Dune
   profile (compile-time, enabled_if) is the sanctioned home for EVERYTHING
   diagnostic — temporary debug prints, env-gated instrumentation, profiling
   drivers, and analysis-forensics tools alike.  It provides the debug
   executables:
   - `zz_scratch_probe/vsa_debug.exe` (fixture traces, views, live maps),
   - `zz_scratch_probe/wbig_diag.exe` (w_big address inspection),
   - `zz_scratch_probe/stage_timer.exe` (per-stage pipeline wall-time
     breakdown: analyze / fixpoint+views / partitioned / walk+merge /
     stack_to_locals / dce — the profiling driver),
   - `zz_scratch_probe/conv_diag.exe` (fixpoint NON-CONVERGENCE diagnosis:
     prints the first still-growing (block, successor), the widening-point
     set, the failing blocks' BIR, and the gap successor's words/memory).
   NEVER add temporary debug prints / env-gated `Sys.getenv` instrumentation
   to production `src/` or `src/cbat_vsa/` code — keep the production sources
   clean; use or extend the debug harness instead.  Build/run:

   ```sh
   dune build --profile vsa-debug zz_scratch_probe/vsa_debug.exe
   dune exec --profile vsa-debug zz_scratch_probe/vsa_debug.exe -- d4
   dune exec --profile vsa-debug zz_scratch_probe/wbig_diag.exe -- /tmp/corpus/<bin>
   dune exec --profile vsa-debug zz_scratch_probe/stage_timer.exe -- <bin> <subname>
   dune exec --profile vsa-debug zz_scratch_probe/conv_diag.exe -- <bin> <subname>
   ```

   Profiling (use perf when `kernel.perf_event_paranoid` allows — else the
   stage_timer differential timing): `perf record -F 1000 --call-graph dwarf --
   dune exec --profile vsa-debug zz_scratch_probe/stage_timer.exe -- <bin>
   <subname>` (the stage_timer links `-g`, so DWARF call graphs work).
   NOTE: stage_timer.ml and conv_diag.ml reference the `hike` library via its
   FLAT internal module names (`Hike__Targetutils`, `Hike__Hike_vsa`, ...),
   NOT the `Hike__.Targetutils` wrapper-namespace form — the ocamllsp
   resolution of the `Hike__` wrapper module (the `module Hike__ = struct
   end` shadow that dune emits for a library whose name collides with its
   main module) is unreliable, so the flat names (direct `.cmi` lookup) are
   used instead.  `.pi-lens.json`'s `ignore` list is empty.
   They build in every profile (never installed, never used by production);
   the other debug executables keep `enabled_if` (they only use `cbat_vsa`).
7. **THE STACK IS LLVM ALLOCAS — SOUND FALLBACK FIRST, PRECISION FOR
   OPTIMIZATION (the user's endgame directive, 2026-08-16).**  Every stack
   access's emission target is a REAL LLVM alloca (or a static variable) —
   never the model's `%frame` + inttoptr arithmetic as the goal.  The model
   frame is only the SOUND FALLBACK: ONE large alloca per sub covers every
   access on every binary (correct, but it defeats LLVM's SROA/alias
   optimizations — so it is the fallback, not the target).  The VSA's
   precision is what enables optimization: the per-access offset ranges split
   the stack into regions; regions the VSA proves NON-OVERLAPPING become
   SEPARATE allocas; overlapping regions MERGE (the write-closed rule —
   together or not at all).  The VSA need NOT be maximally precise — it is
   fine if it sometimes does not converge to the true value (those accesses
   fall back to the big alloca); what matters is that it converges in a LOT
   of functions.  DYNAMIC allocations (VLA/alloca — `RSP := RSP - size` with a
   runtime size) become REAL LLVM `alloca`s with dynamic sizes (the static
   frame cannot contain them — the model arithmetic points below the frame,
   the alloca_vla segfault).  GOAL: the VSA is 100% SOUND and hike converts
   the stack to LLVM allocas / static variables — it should work on EVERY
   binary.

## Build & test

- Root is a dune workspace (`src/`, `test_cbat/`, `zz_scratch_probe/`): `dune build`,
  `dune runtest` (plain-OCaml 315-check suite, no oUnit; prints `ALL CBAT TESTS PASSED`).
- The plugin bundle is the real artifact and must be installed to the opam switch first:
  `dune build @install && dune install`, then `cd src && make` (= `bapbuild hike.plugin -pkg llvm -pkg hike.cbat_vsa` + `bapbundle install hike.plugin`).
- **A stale installed plugin silently runs old code** — after any source change, rebuild
  and reinstall the bundle before running the corpus. **When a library interface changed
  (any `cbat_vsa*` .mli), plain `make` is NOT enough**: bapbuild reuses its cached module
  compiles (hike.ml's mtime is unchanged), shipping a stale interface — run
  `cd src && bapbuild -clean && make` (the 2026-08-13 interface-mismatch gotcha).
- Run: `bap <bin> --pass=hike-convlir --hike-output-file=out.ll` (`--hike-output` also works).
- Toolchain lives in `shell.nix`, but it is stale: its `make sim` hook has no Makefile
  target (ignore that hook; `nix-shell` will fail at the end of setup).

## Pass pipeline (`src/hike.ml`)

Single chain, order enforced by pass deps; only `hike-convlir` is user-facing:

1. `hike-filter` — filters subs (named exclusions, stub/extern/intrinsic,
   intrinsic callers, symbol-table check) — its own pass, FIRST in the chain
   (no pass calls another pass's logic; the chain is deps-only)
2. `hike-relevance` — tags defs (`relevant`, `stack_access`, `dynamic_alloc`)
3. `hike-vsa` — fills `Convutils.vsa_info` (sub tid → per-def SP-relative offset ranges
   plus k-ranges).  Also merges set-overlapping tags into one span
4. `hike-stack-to-locals` — VSA CALCULATES, stack-to-locals only MERGES: collects the
   VSA's per-access stack ranges (the `vsa_info.offsets` tags — the value-based (lo, hi)
   the addresses fall into; `Infinite (lo, hi)` becomes its span), MERGES the
   overlapping ranges into STACK REGIONS (the connected components of the overlap graph
   — a const access whose offset overlaps a ranged access's region lands in the SAME
   merged region, tagged on both), and tags every access with its region.  Then rewrites
   constant-offset stack Load/Store to named locals, plus the address-keyed nested-access
   rewrite (the -O0 cmp pattern reads converted cells through loads nested in BinOp
   defs).  WRITE-CLOSED (the region rule): a region converts TOGETHER or NOT AT ALL —
   every member must have the identical range; any mixed region (a const access
   overlapping a ranged access — the -O0 loop-write / copy-out-read pair, sret_big)
   stays memory.  Over-skip costs precision, never correctness.  No tag
   pruning: the emitter only consults tags whose def's rhs is still a memory access
   (`addr_is_stack`)
5. `hike-dce` — the aggressive DCE lane: replaces the lifted RETURN epilogue
   (`#t := mem[RSP]; RSP := RSP + 8; call #t with noreturn`) with the var-free target so the
   popped-address def dies, then sweeps never-used defs to a fixpoint (the emitter emits a
   real LLVM `ret` regardless)
6. `hike-convlir` — emits LLVM via `bil2llvm.ml`

Tags are Tid-keyed and computed before emission; pass deps must stay prefixed (`hike-...`).

## The stack model (the endgame — user directive, 2026-08-16)

The EMISSION target for every stack access is a REAL LLVM alloca (or a static
variable) — the model's single `%frame` + inttoptr arithmetic is the SOUND
FALLBACK, never the goal.  The hierarchy:

1. **DYNAMIC allocations (VLA/alloca)** — `RSP := RSP - size` with a RUNTIME
   size (the detection: a non-literal RSP decrement; the -O0 corpus shape is
   the direct `RSP := RSP - RAX`, the indirect `RSP := tmp` where `tmp := RSP
   - size` is also handled) → a REAL `alloca i8, i64 <size>`; the model RSP
   local binds to `ptrtoint %vla`; the vla[i] accesses become GEP-able.  The
   static `%frame` CANNOT contain them (the model arithmetic points BELOW the
   frame — the alloca_vla segfault); LLVM's dynamic alloca IS the exact
   semantics.  The size REG being TOP/INF at the fixpoint is fine: the
   downstream addresses stay TOP → no tags → they stay memory (sound), and at
   runtime they point into the real alloca (valid).

2. **Non-overlapping stack regions** — the VSA's per-access offset ranges (the
   `vsa_info.offsets` tags) partition the stack; regions the VSA proves
   NON-OVERLAPPING become SEPARATE `stack_rN` allocas → LLVM can scalarize
   and alias them (the optimization the single-frame model forfeits).
   Overlapping regions MERGE into one alloca (the WRITE-CLOSED rule — a
   region converts together or not at all; a member that stays memory — an
   ABI-visible incoming-arg access — blocks the whole region).

3. **Static variables** — constant-address stack objects that never overlap
   anything become static globals (a future lane).

4. **The sound fallback** — when the VSA cannot bound an access (top/
   infinite), it stays in the model frame (or a large per-sub alloca):
   correct on every binary, unoptimized.

The VSA need NOT be maximally precise: it is FINE if it sometimes does not
converge to the true value — those accesses fall back to the big alloca.
What matters is that it converges in a LOT of functions, so the common case
is optimizable.  GOAL: the VSA is 100% SOUND and hike converts the stack to
LLVM allocas / static variables — it should work on EVERY binary.

## VSA library (`src/cbat_vsa/`)

- Two dune libs: `hike.cbat_vsa_domain` (unwrapped `Cbat_*` modules) and `hike.cbat_vsa`
  (wrapped; re-exports `AI`/`Mem`/`WordSet`). Only `ppx_bap` works under dune 3.23 —
  the upstream 5-ppx set fails to link.
- The restriction is **tag-only** (the 2026-08-10 simplification): there is NO
  `restriction_enabled` switch. `denote_def` skips untagged defs unconditionally — the
  per-def `relevant` tag presence IS the restriction. Production arms it by running
  `Hike_vsa_relevance.analyze` in `hike-relevance` (every production sub is tagged before
  the fixpoint). A raw untagged `static_graph_vsa` tracks nothing — synthetic unit
  fixtures must `tag_all` their subs or run them through `Relevance.analyze`.
- Backward refinement (the L3a/L3c/L-B/M5 lanes, the trace-partitioning design —
  `docs/trace-partitioning-plan.md`): GATE-FREE.  The refinement runs in the Phase B
  post-pass (`edge_views_of` over the converged solution) — the taken/fallthrough
  views per edge, the producer subtraction (`cstr' = cstr ∩ post(v)`) confining each
  pre-image to its own def's produced values, the trace-exact cell meets
  (`constrain_cell_on_trace`).  Every operand/def/shape has a complete rule
  (`operand_constraints`, `def_constraints`); a rule's identity (top / no constraint)
  is the sound answer, never a gate or a bottom.  The forward relevance restriction
  (tag-only) is a forward-domain property, untouched.
- Keep the `set_stack_0` anchor tag; the fixpoint runs in 32-ROUND CHUNKS with a
  CONVERGENCE VERIFICATION between chunks (`convergence_gap` — one extra transfer
  round per chunk checking every CFG successor already contains the merged
  outgoing state) and monotone re-runs up to 64 chunks (2048 rounds; the D.1 fix,
  2026-08-16).  The old silent `~steps:256` cap is GONE as a single-run bound: the
  contextual fixpoint's equality compares `Dep` values by identity so a run always
  iterates its full cap, and slow chains (sequential loops summing past a chunk)
  continue across chunks.  A chain STILL growing after 2048 rounds raises
  `Fixpoint_not_converged` — production (`Hike_vsa.offsets_of_sub`) degrades the
  sub soundly (no tags, every stack access stays real memory) with a warning;
  `conv_diag.exe` pinpoints the growing block.  `not_implemented` always degrades
  to top with a logged warning.
- Widening is LANDMARK-DIRECTED — the FAITHFUL port of Simon & King, "Widening
  Polyhedra with Landmarks" (APLAS 2006), landed 2026-08-23 (v2 replaced the v1
  "rung-extension + two-pass restart" sketch; the static threshold ladder /
  geometric family AND the whole `widen_join_threshold rung machinery —
  hemisphere gate, strict-rung rule — are DELETED, `Cbat_thresholds gone):
  (1) ACQUISITION (paper Listing 1, `observe_unsat in `meet_var): when a guard
  constraint meets a var's value set and the intersection is EMPTY (a disabled
  behavior), the excluded boundary + its distance become a landmark of the
  enclosing WTO cycle (`heads_of_wto maps every block to its innermost SCC
  head; `denote_block_with_stores binds it around the deferred jump
  refinement).  Because a disabled behavior must be observable BEFORE the
  cycle's first widening, `decoded_condition now also decodes the
  COMPLEMENTARY jcc idioms (jg/jge/jbe → SGT/SGE/ULE — `decoder_constraint
  already had all nine rows) so BOTH edges of an -O0 loop guard refine.
  (2) CONSUMPTION (paper fig. 3, in `static_graph_vsa at each head widen):
  `lm_calc_steps (Listing 3) turns the two most recent distance measurements
  into floor(dcur/(dprev-dcur)) traversals — LM_zero (a landmark still awaiting
  its snapshot) → `lm_advance (Listing 2) + plain join; finite steps →
  `AI.selective_widen_extrapolate ~steps (Listing 4, `Clp.extrapolate_steps:
  stable bounds kept, unstable bounds translated by observed growth·steps,
  rounded OUTWARD onto the join's grid; translation overflow → the paper's ∞
  arm = plain widening) + clear this cycle's records; LM_inf →
  `AI.selective_widen (plain widening) + clear.  ONE stabilization pass — no
  restarts.  Distances cap at 2^40; memory cells carry no landmarks (words lane
  only, documented scope).  No on/off switch.  Related fix:
  `Clp.intersection`'s diophantine anchor is clamped to `min_elem p2` (the R2-1
  loose-hull — meet with circular hulls was over-approximating).
- Call abstraction is FRAME-KEEPING (the call-abstraction precision lane —
  `AI.call_abstraction_frame` + `Mem.call_keep`): at a call the caller's own frame
  (cells at key ≥ the call-time RSP, outside the pointer-arg ESCAPE ranges) survives;
  the escape = the SysV integer/pointer arg registers WRITTEN IN THE CALL BLOCK (the
  -O0 arg setup; a never-written register's top value would falsely force the
  whole-memory-top fallback).  The whole-memory top stays the sound fallback for any
  doubt (a non-singleton RSP or an unbounded arg).  The relevance pass tags the
  arg-setup defs (L-E2: RDI/RSI/RDX/RCX/R8/R9 writes — the `RSI := 0` memset arg was
  untagged → the escape saw top → the caller's frame destroyed).  The L-E1 +8 matched-
  pair restore is CONDITIONAL on the call block writing RSP (L-E1b: the FP-intrinsic
  calls — BIR Calls with no stack push — drifted RSP by +8 per intrinsic call;
  measured +0x48/iteration in mixed_fp_int's FP loop → the widen walked it to an
  infinite step-8 CLP).  Together these closed the 9 -O0 corpus w_big (window ≥ 2^63)
  to 1 (alloca_vla's VLA div — the runtime-arm class) at +498 def-exact / −424
  def-top; the -O2 corpus (same sources at -O2) measures 95.05% ldstk exact with 4
  w_big (the NEQ-guard class — `jne` counters can't be refined; the two-sided
  constraint is not CLP-representable).
- The emitter's untagged stack access is now a WARNED POISON (bil2llvm.ml
  "hike: guarded: ... dead-path poison") instead of a `failwith`: the va_arg
  alignment-split dead branch's u128 stores (the concretely-dead misaligned path)
  previously crashed the whole pass; the poison is never executed (the block is
  unreachable).  Corpus: -O0 31/32 rc=0 (fptr_table = the expected indirect-call
  class), -O2 31/31 rc=0; check_allocas 120/0 (-O0) and 124/0 (-O2); semantic
  harness 8/8 PASS.
- Drivers: `dune exec test_cbat/corpus_watch.exe -- <bin>`, `dune exec test_cbat/precision_probe.exe -- <bin>`.
- Env toggles: `HIKE_VSA_DEBUG` (hike.ml stderr), `HIKE_VSA_RESTRICTION=0` (corpus_watch
  only — skips `analyze`, so the untagged fixpoint tracks nothing: the baseline),
  `HIKE_VSA_DIAG_BOTTOM=1` (precision_probe only).  (`HIKE_VSA_ANCHOR=1` and the
  probe's anchored-entry mode were removed 2026-08-13 with the VSA's
  unanchored-mode flag — the frame-correct rewrite is always on.)

## Validation (`scripts/`)

- `compile_corpus.sh` → corpus in `/tmp/corpus`; PIE-ONLY since 2026-08-26
  (user directive "only work on PIE with no fallbacks"): plain
  `gcc -O0 -fno-stack-protector` = distro-style ET_DYN executables. There is
  NO `-no-pie` mode anymore; the script hard-fails if any built binary is not
  `ELF … pie executable`.  The old ET_EXEC-era IR-identity oracle
  (`/tmp/heritage_x1c`) is retired with the recipe switch.
  The list.c main stub is generated under `$OUT/.build/` (never inside the corpus dir).
- `run_corpus.sh [corpus] [out]` → `bap` over the corpus; per-binary `out_*.ll` + a table of
  surviving diagnostics (`hike: guarded:`).
- `check_allocas.sh <out_dir>` → structural asserts on emitted IR: no sp-derived GEP index
  into a `stack_rN` alloca (dynamic loop-index GEPs are fine), no `@stack` global, and one
  `%frame` alloca per memory-touching define (1:1; stack-free defines exempt).  (The old
  vacuous sp-chain tripwire was removed 2026-08-23.)
- `semantic/run_semantic.sh` → llc + `harness.c`, byte-diff stdout vs native, against the
  checked-in `baselines/heritage_baseline_copy` IR; setjmp modules link `setjmp_stub.S`.
  The LIFTED-executable link stays `-no-pie` — a constraint of the harness artifact
  (baked @got.plt constants + extern_weak .rodata refs would force a rejected
  DT_TEXTREL under `-pie`), NOT a corpus fallback; see run_semantic.sh's header.
- `semantic/run_semantic_all.sh` → the same native-vs-lifted gate over EVERY emitted
  `out_*.ll` (not just the fixed 8-bin set); 15 s timeout per run.

## CURRENT VALIDATION STATE — refresh after EVERY change

**Directive (NON-NEGOTIABLE):** after every change to `src/` or `src/cbat_vsa/`, re-run
ALL gates below and rewrite this section with fresh numbers and a fresh timestamp. An
AGENTS.md whose "current state" disagrees with the tree is a doc BUG — the next session
will trust these numbers to distinguish its own regressions from inherited ones (the
2026-08-26 rename_intrinsics incident below is exactly that failure mode).

**Last verified: 2026-08-28 16:35 EEST — Relevance cleanup 01 (.mli + stack_access rename + 4 pure helpers split)**

This commit implements Ticket 01 of the Relevance Cleanup series:
- Created `src/hike_vsa_relevance.mli` exposing `stack_access`, `relevant`, `dynamic_alloc`, `has_stack_access`, `is_sp`, and `analyze`.
- Renamed `direct_sp` -> `stack_access` with a fresh UUID (`44f5cc3f-d8a4-472e-8930-435eea4b6a1d`) and dropped the old name without alias.
- Split `src/hike_vsa_relevance.ml` into four pure helpers: `collect_def_maps` (via single `Term.visitor`), `forward_vars` (SP-only fixpoint with `Var.base` helper and invariant comments), `backward_slice` (reverse fixpoint from stack_access seeds), and `detect_dynamic_alloc`.
- Updated all consumers in `hike_vsa.ml`, `hike_stack_to_locals.ml`, `bil2llvm.ml`, and test fixtures in `test_cbat.ml`.

Corpus emits with **3 surviving `hike: guarded:` u128 warnings**
(va_arg_mixed/@consume_mixed, va_arg_vacopy/@two_pass,
variadic/@sum_n — va_arg alignment-split dead branches, by design).

All gates re-run against the PIE corpus at this commit:

| Gate | Command | Current result |
|---|---|---|
| unit suite | `dune runtest` | **3 FAIL** (LM F1 + LM F2c × 2 — landmark-widening tests; pre-existing, see `.scratch/landmark-directed-widening/`) |
| corpus emission | `bash scripts/run_corpus.sh /tmp/corpus /tmp/heritage_p5` | **31/31 rc=0**, 3 surviving `hike: guarded:` u128 warnings (va_arg alignment-split dead branches) |
| structural asserts | `bash scripts/check_allocas.sh /tmp/heritage_p5` | **124 passed, 0 failed** ✅ |
| semantics (all) | `bash scripts/semantic/run_semantic_all.sh /tmp/corpus /tmp/heritage_p5 /tmp/sem_diag` | **31 PASS, 0 FAIL, 0 SKIP** of 31 emitted ✅ |
| semantics (8-bin) | `bash scripts/semantic/run_semantic.sh /tmp/corpus /tmp/heritage_p5 /tmp/sem_diag` | **8/8 PASS** ✅ |
| probes | corpus_watch / precision_probe over `/tmp/corpus/*` | NOT RE-RUN this session (out of scope) |
| FP micro-suite | fm2/fm4/fm6/fmc8 native-vs-lifted | NOT RE-RUN this session (out of scope) |
| coreutils PIE (103) | `coreutils_pipeline.sh` lift+test | NOT RE-RUN this session (out of scope) |

coreutils residual classification: df/du = live-/tmp drift between captures
(stable-dir reruns byte-identical); vdir = transient (identical rerun);
**dd + getlimits-LDBL-lines are gated on ONE upstream dependency**: BAP's x86
lifter has NO x87 semantics (fldt/fstpt/x87 arithmetic produce no BIL — the
10-byte constant copy never lands in any model slot; verified: zero stores to
those slots in the BIL, zero float ops in dd's human_readable/adjust_value,
zero FLD/FSTP entries in any installed semantics table). Fixing it means
adding x87 (st-array/TOP-pointer) semantics to BAP's lifter — upstream work,
same category as the ET_DYN gap that preceded this session.

**x87 CLI reconnaissance (2026-08-26, do NOT re-investigate)** — the user-suggested
BAP intrinsic switches were evaluated exhaustively, including reading the full
dispatch chain in BAP sources. None is currently usable:
- `--bil-enable-intrinsics=:unknown`: does NOT classify x87 (only ENDBR64
  surfaces); fldt/fstpt are silently dropped without being "unknown".
- `--bil-enable-intrinsics=asm:f…`: surfaces `intrinsic:llvm-x86_64:LD_F80m`
  calls, but via `create_intrinsic` (bil_lifter.ml) whose args are RAW op codes
  (`Reg.code` ints + scale/index/disp fields) — consuming them means
  re-implementing EA decode + an st-stack simulator in hike. Rejected.
- `--x86-with-legacy-floating-points`: a complete legacy FP lifter EXISTS
  (plugins/x86/x86_legacy_fp_lifter.ml, st-array model) but in this build
  (2.6.0-alpha+89bc723) it crashes on arithmetic (`bad_type Imm 79 vs Imm 80`,
  bisected: data-movement ✓, FNSTCW ✓, arith ✗) AND reconstructs no main at
  all (empty modules). Unusable.
- **THE ARCHITECTURALLY RIGHT LANE (the user's suggestion), and its exact
  blocker**: default FP lifting IS Lisp-driven — the x86 plugin creates a
  `Primus.Lisp.Semantics` context on system "x86-floating-points" / feature
  "intrinsic-semantics" (= installed share/bap-common/semantics/*.lisp,
  package llvm-x86_64); the lifter resolves `Lisp.Semantics.name =
  <encoding>:<Insn.name>` and calls the lisp function of the same name,
  passing ONE ARG PER DECODED OPERAND — `Op.Reg r` wires THE REGISTER ITSELF
  (readable AND writable, cf. set-sse dst), `Op.Imm` a static literal,
  `Op.Fmm` unknown (primus_lisp_main.ml `args_of_ops`). Adding `(defun
  LD_F80m …)` entries would therefore lift fld/fstp into REAL BIL with zero
  hike changes — EXCEPT the lisp dialect has no mutable globals and the amd64
  target defines NO ST(0..7)/TOP registers (verified: no such strings in
  bap_x86.cma; no defvar in the DSL), so the required cross-instruction st
  state is inexpressible. UPSTREAM UNLOCK (one change): define ST0..ST7(+TOP)
  in BAP's amd64 target description; then ~30 lines of lisp (load-mem/
  store-word pairs + the existing ieee754 intrinsics for arith) implement the
  whole lane with no hike involvement. Revisit on a BAP upgrade.

PIE-era notes (unchanged from earlier today): the heritage byte-identity oracle
is retired (pre-PIE corpus); semantic gates are the identity oracle; reference
PIE emissions: `/tmp/pie_x1` (pre-fix), `/tmp/pie_x2` (post-fix).
- `/tmp/simplify_fixed` holds the 2026-08-26 reference emission matching the table above.

### Incident record

- **2026-08-26 — `rename_intrinsics` found UNWIRED from the filter pass (FIXED same day).**
  The Bug C width-suffix canonicalizer was defined in `hike.ml` but never called:
  `filter_subs` ran only `simplify_defs |> simplify_jmps`. Interface temps kept their
  lifter names (`intrinsic:x0`) while the emitter's FP-intrinsic operand fetch resolves by
  the WIDTH-SUFFIXED prefix (`intrinsic:xN_<w>`, see [Bil2llvm.create_native_fp_call]), so
  every body-less mapped-FP call failed loudly at emission: `mixed_fp_int`,
  `union_overlap`, `va_arg_mixed` all died with `hike: no intrinsic:x0_ binding`
  (28/31 corpus binaries still emitted, byte-identical to the oracle — which is how the
  regression stayed invisible until a full re-run). Fix: restore the documented wiring,
  `sub |> rename_intrinsics |> simplify_defs |> simplify_jmps` in `filter_subs`. Proof of
  exact restoration: post-fix emission is **byte-identical to `/tmp/heritage_x1c` on all
  31 binaries**, and allocas/semantic return to the recorded 124/0 and 31/31. LESSON:
  "green last week" is not a property of the tree — only a re-run against the oracle is;
  keep this section's timestamp honest.

### Known regressions under investigation (recorded 2026-08-24)

### X1-d — UNTAGGED ABSOLUTE-IMMEDIATE SECTION ADDRESSES (OPEN, by design —
recorded 2026-08-25, coreutils full-pipeline run).
**Mechanism:** gcc -no-pie sometimes materializes a DATA address as an
ABSOLUTE IMMEDIATE (`mov $0x4065b8,%edx`) instead of a taggable `lea
rip+…`. The lifted BIL arrives as a plain `RDX := 0x4065b8` — and an
immediate carries NO address/data intent. The tagged rip-relative forms
remap correctly (`rip_relative_addr` → `create_rip_relative_addr`), but
these have no tag, so the raw constant escapes into the emitted IR
(`@gettext(i64 4220344, …)`). The lifted binary's own section layout
differs from the native one, so the constant lands mid-.text
(`0x4065b8` = native .rodata string → lifted `c_strcasecmp+2024`) and
the "format string" prints as code bytes.
**Impact scope:** every tool whose DEFAULT invocation prints a diagnostic
through the error()→gettext path — 86/108 coreutils-9.5-tarball tools
(basename/chgrp/chmod/cksum/comm/…); tools silent at default invocation
pass (echo/cat/tee/…). The corpus is unaffected (fixtures print no
diagnostics); the earlier 9.10-git build was unaffected (its codegen used
tagged rip-relative forms on these paths — same gcc, different source
version/instruction selection).
**Why NOT fixed (doctrine):** remapping immediates by section-range
membership (lo ≤ v ≤ hi → GEP into @section) would be a GUESS — a genuine
numeric constant colliding with a section span would be silently
corrupted into a pointer. There is no sound tag at the BIL level; the
attempted range hook in [create_immidiate] was REVERTED for exactly this
reason.
**Possible future lanes:** (1) a disassembler-byte-level tag pass: read
the ORIGINAL instruction encodings (BAP insns) and mark Imms that were
`mov $abs` of mapped-section addresses — precise, non-trivial plumbing;
(2) ~~lift PIE-produced binaries once ET_DYN support lands~~ DONE as the
VALIDATION target 2026-08-26: the entire script/probe chain now compiles,
lifts and tests PIE (ET_DYN) EXCLUSIVELY (PIE only, no fallbacks) —
PIE codegen uses rip-relative forms only, so this class is structurally
absent on every PIE input (see CURRENT VALIDATION STATE); (3) document per-build guidance: binaries
built where the absolute-immediate form appears on diagnostic paths will
show garbage messages while all computation stays correct (verified:
computation/results are byte-exact on the passing subset).

- ~~`two_pass` (`va_arg_vacopy`) NO LONGER CONVERGES~~ **RESOLVED 2026-08-25**:
  root cause was the emitter-side missing retaddr pop — every executed call
  leaked 8 bytes of model-RSP (see the L-E1e entry below), and the drift
  perturbed the fixpoint's convergence surface. After `restore_sp_after_call`
  landed, a fresh `bap` run of `/tmp/corpus/va_arg_vacopy` shows ZERO
  not-converged warnings and `run_corpus.sh` reports rc=0 with no surviving
  diagnostics. Original investigation notes kept for the record: PROVEN a
  regression by the checked-in baseline stderr logs
  (`baselines/heritage_baseline_copy/err_*.txt`): zero not-converged corpus-wide,
  and baseline `err_va_arg_vacopy.txt` shows a CONVERGED `two_pass` (its normal
  `hike: guarded:` def-poison diagnostic). Suspect window had been the
  UNRECORDED Aug-24 ~00:00–04:00 batch: `cbat_map_lattice.ml`,
  `cbat_ai_representation.ml`, `cbat_fin_set.ml`, `cbat_vsa.ml`,
  `hike_vsa_relevance.ml`.
- ~~`out_va_arg_mixed` fails `run_semantic_all`~~ **RESOLVED 2026-08-25** by
  the same fix: `run_semantic_all.sh` is now **31/31 PASS** on the fresh
  `/tmp/heritage_spfix` emission (the lifted binary no longer reads the
  register-save-area XMM slot as 0.0). The drift had corrupted the
  register-save-area addressing between the readdir-class call sequences;
  with sp restored post-call the store/load pair lands correctly.
  Root cause + fix: the L-E1e entry below.

- `src/Makefile clean` deletes every non-`.c`/`.h` file under `src/progs/` — move artifacts
  out first. `*.ll` is gitignored except `baselines/**`.

### L-E1e — the emitter-side retaddr pop (landed 2026-08-25) — BUG A of the coreutils probe

**Bug:** every executed call leaked 8 bytes of model-RSP. BAP's x86 call
expansion emits ordinary caller-block defs (`RSP := RSP - 8; mem[RSP] :=
retaddr`) but nothing pops them: a lifted callee starts from its OWN fresh
[%frame] anchor (`build_entry_block`), so its ret restores the CALLEE's lane,
and external callees have no model lane at all. The VSA's `frame_add_rsp`
(`cbat_ai_representation.ml`) does the +8 abstractly (L-E1 matched-pair), so
the analysis modeled correct-x86 while the emission drifted — after N calls
the concrete sp was `entry - 8N`. Machine-proven on coreutils: `ls print_dir`
model-rsp descended monotonically (~32–40 B/loop-iteration at the readdir push
sites); once it crossed ~2.9 KB below the anchor (frame alloca only 848 B) the
push itself wrote llc's spill slots (hardware-watchpoint catch:
`movq $0x408766,(%rax)` trampled the spilled anchor copy) → garbage DIR* →
SIGSEGV in `readdir64`; same fingerprint in `sort inittables`. Short-lived
binaries survived inside frame padding; `yes`-class infinite loops crashed
regardless of static depth.

**Fix:** `restore_sp_after_call` in `bil2llvm.ml` — after EVERY emitted call
(direct `create_func_call`, indirect `create_indirect_call`; FP-return arms
included) rebinds the caller's sp local to `post_push + 8`. Uniform over
internal/external (a lifted callee can never pop the caller's lane); idempotent
where threading was already correct; VLA/prologue `RSP := RSP - k` defs are NOT
touched; `[hike_stack]` still receives the post-push value (read during arg
collection) so `[+8..]` incoming-arg aliasing is byte-identical; FP-intrinsic
calls never reach the emitters (inlined via `create_native_fp_call`, their BIR
carries no push). NOTE: the push itself still emits and DCE keeps it by policy
("memory writes and ABI registers are always kept", `hike_dce.ml` header) —
with the restore the push traffic is bounded (stores land on fixed slots near
the anchor), so removing the CALL-push pattern outright (symmetric to the
existing RETURN-epilogue rule) is an optional optimization lane, not needed for
correctness.

**Verification (all green 2026-08-25):** `dune runtest` ALL PASSED;
fresh emission `/tmp/heritage_spfix`: `check_allocas.sh` **124/0**,
`semantic/run_semantic_all.sh` **31/31** (incl. `va_arg_mixed`, see resolved
above); `ls` readdir-loop sp FLAT across iterations (`0x7ffffffeded8` constant,
DIR* valid every hit); `sort` sorts, `dircolors` byte-identical.

### X1-c — the mapped-FP-intrinsic stub signature + the COMISS table gap (landed 2026-08-25)

**Bug 1 (hike side, `src/hike.ml`):** BAP expands only the core-theory-standard
soft-float names (fadd/fsub/fmul/fdiv/frem) into real bodies; every
cast/convert class (`cast_sfloat_{32,64}`, `cast_float_{32,64}`,
`cast_sint_{32,64}`, `fconvert_{32,64}`) arrives as a BODY-LESS intrinsic stub.
`should_filter` dropped them (plain `is_intrinsic` attr), so `ctx.subs` never
received their signature and `get_args`/`get_rets` fell back to SysV: at every
mapped call site arg0 evaluated as **RDI** instead of following the in-block
`intrinsic:x0 := <src>` def, and rets `[RAX;RDX]` made `create_native_fp_call`
silently discard the computed native result. Net effect: cvtsi2ss converted RDI
(harness-zero) instead of RAX → gnulib `compute_bucket_size(103) = 0 →
next_prime(0) = 0 buckets → hash NULL cascade → xalloc_die "memory exhausted"
(du cp df sum ls; div.c nc=0). **Fix:** classify by the emitter's mapping, not
body presence — new predicate `mapped_fp_intrinsic` (= name maps in
`Bil2llvm.native_fp_op`); such subs are kept out of the filter and
`compute_sub_sig` synthesizes the model interface by arity (binops [x0;x1],
unary casts [x0]; rets [y0]; all u64 — sig_diag-proven against the working
body-ful models). Adding Primus-Lisp `_32` defuns was proven a dead end (site-
lisp is not consulted for these subs; verified empirically).

**Bug 2 (semantics table, installed
`share/bap-common/semantics/x86-64-sse-intrinsics.lisp`):** `COMISS`/`COMISD`
had NO entries — the lifter silently dropped the instruction and conditional
branches consumed stale integer flags (compute_bucket_size's `jae` on stale
CF=0 → wrong path regardless of the division result). Also fixed the rr
`fp-compare` macro typo (`(compare-floats rt rm rm)` compared a register with
itself, dropping rn). Added COMISD{rm,rr}/COMISS{rm,rr} with the UC-identical
BIL semantics (they differ only in signalling-NaN exceptions).

**Verification (all green 2026-08-25):** `dune runtest` ALL PASSED; fresh corpus
emission `/tmp/heritage_x1c`: every binary rc=0 with zero surviving diagnostics,
`check_allocas.sh` **124/0**, `semantic/run_semantic_all.sh` **31/31**;
coreutils spot-checks byte-identical to native: du -s (8), cp file copy, df full
mount table, sum checksum, ls 300-file sorted listing (md5-equal), plus
/tmp/flt/div2 int→f32 cast + fdiv exact (bits=4300c000).

### Coreutils probe status (103 binaries, `/tmp/opencode/coreutils-test`, recorded 2026-08-25)

Pipeline `scripts/coreutils_pipeline.sh` (clone→build −O0 −no-pie→lift→llc+harness
→native-vs-lifted byte-diff; workdir default `/tmp/opencode/coreutils-test`).
Lift 103/103 OK. Semantic 85 PASS / 18 FAIL → failure classes fully mapped:

- **Harness false positives, FIXED in the script**: mktemp random-suffix and dd
  elapsed/rate-mantissa now normalized before the diff (the dd rate UNIT stays
  visible — a kB/QB mismatch still fails); capture cap shrinks-only (was
  zero-padding every short output to exactly 1 MiB).
- **BUG A (sp leak)** — FIXED, see L-E1e above. Cleared: ls dir vdir sort sum
  tail who ptx df dircolors cksum yes crash class.
- **NEWLY UNMASKED (previously hidden behind the readdir-loop crash)** —
  **RESOLVED 2026-08-25 by X1-c** (below): `ls` (mpsort/strcoll NULL crash),
  `sum` (NULL-base write in output_bsd), du, cp, df — all were the X1 class:
  gnulib hash_initialize's compute_bucket_size returning garbage. With the
  fix: du -s, cp file-copy, df full table, sum checksum, and ls's 300-file
  sorted listing are all byte-identical to native.
- **BUG B (poison reaches live values), OPEN:** phantom soft-float input params
  (`@compute_bucket_size(i64 %"intrinsic:y0", i64 %RDI, i64 %RSI, i256 %YMM0,
  i256 %YMM1)` — bodies READ those lanes; sources incl. pxor-style self-XOR
  modeled as read) get `poison` from callers (`bil2llvm.ml` get_local None);
  gnulib `compute_bucket_size` returns 0 → `hash_initialize` NULL cascade →
  xalloc_die "memory exhausted": du paste cp. Causality proven by
  poison-neutralized rebuilds (exhaustion vanishes in all three, next poison
  sink surfaces: `__cxa_atexit(func=NULL)` — an INTEGER arg lane also missing).
- **BUG C (float-width corruption on the YMM↔extern-FP boundary), RESOLVED
  2026-08-25 (the x032/x064 fix).** Root cause chain, fully proven:
  (1) **BAP vars are WIDTH-BLIND** — `Var.equal`/`compare`/`Var.Map` key on
  the NAME only (var_eq probe: same-name u32/u64 vars give `equal=true`,
  `map-size=1`). (2) The lifter's interface temps exploit width polymorphism:
  SS-class writebacks read a u32 `intrinsic:y0`, SD-class writebacks
  (`cvtss2sd`) a distinct-but-name-equal u64 one — every def well-typed
  256→256 (ymm_defs probe), so the BIR was never wrong. (3) hike's maps
  collapse them into ONE lane; whichever width materialized first (u32)
  served every read, and update_phi coerced the correctly computed i64 SD
  result down to i32 — the double lost its exponent half
  (`128.75 = 0x405CC000_00000000` → 0).
  **Fix, two coordinated halves:**
  - **Table level (BAP configuration):** `sse-binary` now appends the RESULT
    width to the intrinsic name (`fadd_rne_ieee754_binary_32` vs `_64`),
    mirroring what `sse-convert` always did — so addss/addsd map to DISTINCT
    width-homogeneous subs. `native_fp_op` maps both suffixed and legacy
    unsuffixed names.
  - **hike level:** `rename_intrinsics` (filter stage) canonicalizes every
    interface temp to its width-suffixed name, so each width threads its OWN
    phi network and no lookup can conflate lanes;
    `create_native_fp_call` resolves x-operands from the MOST-RECENT
    `intrinsic:xN_*` def in-block (binding width varies by table entry:
    CVTSI642SS coerces x0→u64, CVTSS2SD →u32) and binds EVERY consumer-width
    view of the result (y0_64/y0_32/y0_1) at the call block.
  **Verification:** div.c prints `nc=128.750000 dnc=128.750000`; doubles
  exact incl. printf boundary (`bits=4008000000000000` = 3.0);
  `dune runtest` ALL PASSED; corpus all rc=0 zero surviving diagnostics;
  `check_allocas.sh` 124/0; `run_semantic_all.sh` 31/31.
  NOTE: `/tmp/opencode/coreutils-test` was lost in a /tmp wipe — re-run
  `scripts/coreutils_pipeline.sh` for the final du/cp/df/sum/ls spot-check.
- **Latent risk (not triggered):** sub signatures emit params in ALPHABETICAL
  register order (`@hash_initialize(%R8,%RAX,%RCX,%RDI,%RDX,%RSI)`) — safe for
  direct calls (by-name binding through positional slots) and for this corpus's
  escaped callbacks (2-arg comparators sort SysV-coincident), but any
  address-escaped sub whose free-vars don't sort SysV-order breaks positionally.
  Canonicalize to SysV order when convenient.

## Running the test probes & semantic harness

Every probe is a **`dune exec` target** — do NOT run the built
`_build/default/**/*.exe` directly: a bare `.exe` can't find BAP's plugin
path (`Failed to load plugin "x86": Not_found`), and only `dune exec` wires
up the findlib/plugin environment.  `stage_timer`/`conv_diag` and every
binary-analyzing probe use the `hike` library and build in the DEFAULT
profile; only `vsa_debug`/`wbig_diag` are `enabled_if` in the `vsa-debug`
profile.

Prerequisites (once):

```sh
dune build                                              # all default-profile probes
# the two vsa-debug-only probes:
dune build --profile vsa-debug zz_scratch_probe/vsa_debug.exe zz_scratch_probe/wbig_diag.exe
bash scripts/compile_corpus.sh                          # -> /tmp/corpus
```

### Debug-harness fixture mode (no binary needed)

```sh
dune exec --profile vsa-debug zz_scratch_probe/vsa_debug.exe -- d4
```

### Binary-analyzing probes (against a `/tmp/corpus` bin)

```sh
B=/tmp/corpus/factorial
dune exec zz_scratch_probe/probe_loop.exe       -- "$B"
dune exec zz_scratch_probe/probe_cell.exe       -- "$B" main
dune exec zz_scratch_probe/dump_tags.exe        -- "$B" main
dune exec zz_scratch_probe/dump_bil.exe         -- "$B" main
# vsa-debug profile only:
dune exec --profile vsa-debug zz_scratch_probe/wbig_diag.exe -- "$B"
dune exec zz_scratch_probe/probe_wbig2.exe      -- "$B"
dune exec test_cbat/corpus_watch.exe            -- "$B"
dune exec test_cbat/precision_probe.exe         -- "$B"
```

### Timing + non-convergence diagnosis (default profile)

```sh
dune exec zz_scratch_probe/stage_timer.exe -- "$B" main   # per-stage wall-time breakdown
# perf alternative (needs kernel.perf_event_paranoid to allow it):
perf record -F 1000 --call-graph dwarf -- dune exec zz_scratch_probe/stage_timer.exe -- "$B" main
dune exec zz_scratch_probe/conv_diag.exe   -- "$B" main   # fixpoint non-convergence
```

### Semantic harness (native-vs-lifted; the 8/8 oracle)

The harness **never re-emits** — it operates on IR produced by
`run_corpus.sh`.  For a fresh-build validation, emit first, then run the
harness against the FRESH IR (the default 2nd arg is the checked-in
regression baseline `baselines/heritage_baseline_copy`):

```sh
dune build @install && dune install                          # fresh plugin (see Build & test)
bash scripts/run_corpus.sh /tmp/corpus /tmp/heritage_p5       # emits out_*.ll
bash scripts/check_allocas.sh /tmp/heritage_p5                # structural asserts
bash scripts/semantic/run_semantic.sh /tmp/corpus /tmp/heritage_p5 /tmp/sem_out
# expected: 8/8 "PASS <name> (stdout byte-identical)"
```

Per binary it renames `@main`→`@hike_main` (and the crt1-colliding
`@_dl_relocate_static_pie`), `llc -O0 -filetype=obj`, links with
`harness.c` (plus `setjmp_stub.S` when the module uses setjmp/longjmp),
runs lifted vs native, and byte-diffs stdout.  Needs `llc` + `gcc`.

## Gotchas

- `hike_vsa_relevance.ml` is single-sourced (R8, 2026-08-19): `src/` (production,
  the restored two-pass D-2f tagger) is the ONLY copy.  `test_cbat/` and the
  `zz_scratch_probe/` debug probes link the wrapped `hike` library and reach it via
  the flat `Hike__Hike_vsa_relevance` name (or `Hike__.Hike_vsa_relevance`), passing
  `sp` explicitly (`Targetutils.sp (Project.target proj)` / a fixture's `v64 "RSP"`).
  The old single-pass copies in `test_cbat/` and `zz_scratch_probe/` were deleted.
- `docs/vsa-usage.md` §2 is stale: it claims the VSA is not wired into the production pass.
  The relevance/vsa/stack-to-locals/dce passes now ship inside `hike-convlir`; §1's
  `restriction_enabled` ref and the "279-check" count are stale too (tag-only design,
  269 checks). §3 (drivers, API, expected numbers) and the env toggles are still accurate.

## Agent skills

### Issue tracker

Local markdown issues under `.scratch/`. See `docs/agents/issue-tracker.md`.

### Triage labels

Default five-label vocabulary (needs-triage, needs-info, ready-for-agent, ready-for-human, wontfix). See `docs/agents/triage-labels.md`.

### Domain docs

Single-context layout (one CONTEXT.md + docs/adr/ at repo root). See `docs/agents/domain.md`.
