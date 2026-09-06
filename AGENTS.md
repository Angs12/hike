# AGENTS.md — hike

BAP (OCaml/dune) plugin that lifts x86-64 ELF binaries to LLVM IR (the `hike-convlir`
pass), backed by a vendored port of CBAT's value-set analysis (`src/cbat_vsa/`).
There is no README; `docs/*.md` and `docs/adr/*.md` are the design record.
**DOC BUG (recorded 2026-08-31):** `docs/hike-full-plan.md` — the "single
source of truth" for the stack-model endgame, the Option-B fixes, and the
O-series performance plan (O1 done, O2-O4 approved-pending, O5-O7 planned)
— is GONE and was NEVER COMMITTED (no git history; the O-series proposals
are unrecoverable from the repo). `.slim/deepwork/*.md` is likewise absent.
The surviving plan record is `docs/trace-partitioning-plan.md`,
`docs/adr/`, and `.scratch/*/`. The O-series was partially succeeded by the
coreutils differential gate in `.scratch/restriction-removal/spec.md` §5.

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
6. **Debug instrumentation is NOT COMPILED INTO the production binary**
   (restated 2026-09-03, branch `diag-channel` — the grilling-settled regime;
   the old text is below for the record).  The line is: any RUNTIME-VARIABLE
   behavior is debug; production emits FIXED diagnostics only, through ONE
   sanctioned channel:
   - **`Hike_diag` (src/hike_diag.ml) is the ONLY output channel in `src/`**
     — `Hike_diag.warn` prepends the load-bearing `hike:` prefix (the family
     `run_corpus.sh` greps).  The vendored library keeps BAP's `Event.Log`
     (its `not_implemented` eprintf duplicate is DELETED — one channel).
     Direct `eprintf`/`print_endline`/`printf` anywhere else in production
     sources is a VIOLATION; operator-facing control belongs in a BAP pass
     parameter (`--hike-output-file`), NEVER an env var.
   - **Debug output lives behind cppo's `#ifdef VSA_DEBUG ... #endif`** in the
     .ml source (line-level, already in the switch).  The chain is
     `src/cppo_preprocess.sh`: `cppo [-D VSA_DEBUG] | ppx-jane -impl -`,
     keyed by dune's `%{profile}` — in every non-vsa-debug build the blocks
     VANISH from the text stream before the compiler ever sees them.  ppx-jane
     IS the old `pps ppx_bap` driver (it regenerates `[@@deriving equal]`'s
     `equal_vsa_kind` etc.), so cppo must run BEFORE it, never replace it.
   - **The build BLOCKS violations** (`src/check_instrumentation.sh`, wired
     into `src/dune` on aliases `all` and `install`): rule 1 = zero-exemption
     grep for env reads (`Sys.getenv` in any form); rule 2 = comment-aware
     scan for direct prints outside `Hike_diag` (lines inside `#ifdef
     VSA_DEBUG` are skipped — that IS the sanctioned mechanism; `sprintf`/
     `asprintf` are fine).  `dune build` and `dune build @install` both fail
     rc=1 on a violation.
   - **The debug build is opt-in and cheap**: `dune build --build-dir
     _build-debug --profile vsa-debug ...` — its own build dir, so neither
     build evicts the other (measured: without this, every profile switch is
     a FULL 10-22s rebuild in both directions; with it, switching is
     incremental).  Forensics prints (the region-NOT-convertible dump, the
     member-NOT-direct print, the vsa/stl tag counts) fire only there.
   - **The plugin is built by DUNE ENTIRELY** (`(plugin (name hike)
     (libraries hike) (site (bap-common plugins)))` in src/dune, since
     2026-09-03): bapbuild/bapbundle are RETIRED — bapbuild compiles through
     its own ocamlfind pipeline and could not see dune's preprocessing (a raw
     `#ifdef` reached the OCaml parser), and its stale-module-cache class is
     the 2026-09-02 poison-phi incident.  ONE pipeline owns everything.
     PREREQ: the `llvm` package ships no `llvm.cmxs`/META (a plugin
     dynlinking Llvm symbols fails) — `src/backfill_llvm_cmxs.sh` builds it
     with bapbundle's own recipe (`ocamlopt -shared -linkall llvm.cmxa
     libllvm_*.a`, byte-identical 501008 bytes) and backfills the switch's
     `lib/llvm/`; run once (idempotent) after installing the llvm package.
     The old `hike.plugin` bundle zip must be removed (`bapbundle remove
     hike`) or bap loads BOTH and dies (`Hashtbl.add_exn got key already
     present hike`).
   - `src/record_provenance.sh` (run after `dune build @install && dune
     install`) writes `hike.cmxs.provenance` (tree, git describe, src sha16, bundle
     sha16) NEXT TO the installed plugin — battery.sh verifies it before
     running gates; an mtime-based check cannot catch a plugin built from a
     DIFFERENT tree (measured: identical sources, stale artifacts, mtime
     warning silent, corpus rc=0 — only the -O0/-O2 semantic agreement
     caught it).

   The debug executables (build in every profile; `enabled_if` vsa-debug for
   vsa_debug/wbig_diag; NEVER installed, NEVER on a production path):
   - `zz_scratch_probe/audit02.exe` (legacy harness entry, default profile),
   - `zz_scratch_probe/vsa_debug.exe` (fixture traces, views, live maps),
   - `zz_scratch_probe/wbig_diag.exe` (w_big address inspection),
   - `zz_scratch_probe/stage_timer.exe` (per-stage pipeline wall-time
     breakdown: analyze / fixpoint+views / partitioned / walk+merge /
     stack_to_locals / dce — the profiling driver),
   - `zz_scratch_probe/conv_diag.exe` (fixpoint NON-CONVERGENCE diagnosis:
     prints the first still-growing (block, successor), the widening-point
     set, the failing blocks' BIR, and the gap successor's words/memory),
   - `zz_scratch_probe/dump_tags.exe` (vsa_info tag + split_plan dump).
   The dead one-shot stubs (probe_loop, probe_cell, dump_bil, probe_wbig2)
   were deleted in the 2026-08-31 harness restoration — they duplicated the
   above probes' functions.  NEVER add temporary debug prints / env-gated
   `Sys.getenv` instrumentation to production `src/` or `src/cbat_vsa/` code —
   keep the production sources
   clean; use or extend the debug harness instead.  Build/run:

   ```sh
   # the debug build keeps its own dir — neither build evicts the other:
   dune build --build-dir _build-debug --profile vsa-debug zz_scratch_probe/vsa_debug.exe
   dune exec --build-dir _build-debug --profile vsa-debug zz_scratch_probe/vsa_debug.exe -- d4
   dune exec --build-dir _build-debug --profile vsa-debug zz_scratch_probe/wbig_diag.exe -- /tmp/corpus/<bin>
   dune exec --build-dir _build-debug --profile vsa-debug zz_scratch_probe/stage_timer.exe -- <bin> <subname>
   dune exec --build-dir _build-debug --profile vsa-debug zz_scratch_probe/conv_diag.exe -- <bin> <subname>
   ```

   Profiling (use perf when `kernel.perf_event_paranoid` allows — else the
   stage_timer differential timing): `perf record -F 1000 --call-graph dwarf --
   dune exec --profile vsa-debug zz_scratch_probe/stage_timer.exe -- <bin>
   <subname>` (the stage_timer links `-g`, so DWARF call graphs work).
   NOTE: stage_timer.ml and conv_diag.ml reference the `hike` library via its
   FLAT internal module names (`Hike__Hike_vsa`, ...) — the ocamllsp
   resolution of the `Hike__` wrapper module (the `module Hike__ = struct
   end` shadow that dune emits for a library whose name collides with its
   main module) is unreliable, so the flat names (direct `.cmi` lookup) are
   used instead.  `.pi-lens.json`'s `ignore` list is empty.
   They build in every profile (never installed, never used by production);
   the other debug executables keep `enabled_if` (they only use `cbat_vsa`).
      All probe executables documented in this section now BUILD and RUN
   (harness restored 2026-08-31 — see section "Running the test probes"):
   the `dune-project` declares the `vsa-debug` profile, and
   `zz_scratch_probe/dune` carries the full stanza list. The dead stubs
   (probe_loop, probe_cell, dump_bil, probe_wbig2) were deleted rather than
   ported — they duplicated `audit02`/`dump_tags`/`stage_timer`/`conv_diag`/
   `wbig_diag`.


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
8. **STRICT CONTEXT.md ADHERENCE & NO AD-HOC BIL PATTERN MATCHING.**
   - **No AST Pattern Matching for Memory or Registers**: Never write structural `match` patterns over BIL constructors (`Bil.Load`, `Bil.Store`, `Bil.Cast`, etc.) or inspect memory operands directly. Use `Exp.visitor` or `Term.visitor` exclusively.
   - **Target-Defined Stack Pointer (`Abi.sp`)**: Never hardcode register strings like `"RSP"` or `"RBP"` or check for frame pointers. `Abi.sp` is the sole origin for stack derivation. (2026-08-31: `Targetutils` and `Calling_conventions` are DELETED — the standalone `Hike_abi` library (unwrapped, module `Abi` inside each consumer via a one-line alias; exported as `Hike.Abi`) is the ONLY home of register lists, register predicates, and convention facts, shared by the vendored VSA libraries and production. NOTE: the module must never be named `Abi` at the LIBRARY level — BAP ships its own core `abi` plugin (module `Abi`, dynlinked into every bap process), and a bundle-internal `Abi` fails at load with "interface mismatch on Abi"; hence the library/module `hike_abi`/`Hike_abi`.)
   - **100% VSA Tagging Invariant**: Every definition with a `stack_access` tag MUST receive a `vsa_info` tag (`Range`, `Infinite`, `Unbounded`, `Dead`, or `VLA`). Untagged stack accesses are strictly prohibited.
   - **Lattice and Abstract Domain Values**: Dataflow propagation must operate over abstract sets and lattice values, distinguishing pointer arithmetic from memory values without AST inspecting hacks.


## Build & test

- Root is a dune workspace (`src/`, `test_cbat/`, `zz_scratch_probe/`): `dune build`,
  `dune runtest` (plain-OCaml 315-check suite, no oUnit; prints `ALL CBAT TESTS PASSED`).
- The plugin is built BY DUNE ENTIRELY (since 2026-09-03, branch
  `diag-channel`): the `(plugin (name hike) (libraries hike) (site
  (bap-common plugins)))` stanza in `src/dune` + `dune build @install && dune
  install`. bapbuild/bapbundle are RETIRED (bapbuild compiles through its own
  ocamlfind pipeline — it could not see dune's cppo preprocessing, and its
  stale-module-cache class is the 2026-09-02 poison-phi incident; one
  pipeline owns everything now, so the old `bapbuild -clean` ritual and the
  2026-08-13 interface-mismatch gotcha are structurally gone).
  PREREQ (once per switch, idempotent): `bash src/backfill_llvm_cmxs.sh` —
  the `llvm` opam package ships no `llvm.cmxs`/META, so the plugin's Llvm
  symbols cannot dynlink without the backfill (the script builds it with
  bapbundle's own recipe). Remove any legacy bundle first:
  `bapbundle remove hike` (both installed = `Hashtbl.add_exn` at load).
  After any source change: `dune build @install && dune install` — dune's
  content-hash cache is SOUND (it recompiles exactly what changed; there is
  no second cache to go stale), and `src/record_provenance.sh` (run manually
  after install) writes the provenance record the battery verifies.
- Run: `bap <bin> --pass=hike-convlir --hike-output-file=out.ll` (`--hike-output` also works).
- Toolchain lives in `shell.nix`, but it is stale (its setup hook fails at
  the end; ignore).

## Pass pipeline (`src/hike.ml`)

Single chain, order enforced by pass deps; only `hike-convlir` is user-facing:

1. `hike-filter` — filters subs (named exclusions, stub/extern/intrinsic,
   intrinsic callers, symbol-table check) — its own pass, FIRST in the chain
   (no pass calls another pass's logic; the chain is deps-only)
2. `hike-relevance` — tags defs (`relevant`, `stack_access`, `dynamic_alloc`).
   **REMOVAL SPEC'D (2026-08-31, not yet implemented):** per
   `docs/adr/0003-remove-restriction-vsa-seeding.md` +
   `.scratch/restriction-removal/spec.md`, this pass is DELETED — every def
   denoted; `vsa_info` (the VSA's two-channel frame-residency proof) becomes
   the only carrier of stack-access-ness; VLA detection moves into
   `cbat_vsa`; `hike-vsa`'s dep becomes `hike-filter`
3. `hike-vsa` — fills `Convutils.vsa_info` (sub tid → per-def SP-relative offset ranges
   plus k-ranges) by COMPOSING the ONE producer chain (arch review #1, ADR 0005):
   `fixpoint → Cbat_vsa.Cbat_extraction.extract` (the M6 classification walk, the kind
   enum — `Convutils.vsa_kind`'s physical home — the k-range arithmetic, the
   set-overlap merge, the VLA matcher) `→ Hike_stack_model.{frame_escapes, regions_of_sub,
   split_plan}` (the pure stack model, split from the rewrite pass).  The record is built
   complete at one site; `hike_vsa` keeps only the pass policy (Relevance tagging, the
   degraded/non-converged arms, the 100%-invariant gap WARN)
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
- The restriction is **tag-only** — **REMOVAL SPEC'D (2026-08-31, not yet implemented)**: `docs/adr/0003-remove-restriction-vsa-seeding.md` + `.scratch/restriction-removal/spec.md` delete the `relevant` tag, the `hike-relevance` pass, and the backward-lane refineable gates entirely; `vsa_info` (the VSA's two-channel frame-residency proof) becomes the only carrier of stack-access-ness. Until it lands, the tag-only restriction stands: `denote_def` skips untagged defs unconditionally — the per-def `relevant` tag presence IS the restriction. Production arms it by running `Hike_vsa_relevance.analyze` in `hike-relevance` (every production sub is tagged before the fixpoint). A raw untagged `static_graph_vsa` tracks nothing — synthetic unit fixtures must `tag_all` their subs or run them through `Relevance.analyze`.
- Backward refinement (the L3a/L3c/L-B/M5 lanes, the trace-partitioning design —
  `docs/trace-partitioning-plan.md`): GATE-FREE.  The refinement runs in the Phase B
  post-pass (`edge_views_of` over the converged solution) — the taken/fallthrough
  views per edge, the producer subtraction (`cstr' = cstr ∩ post(v)`) confining each
  pre-image to its own def's produced values, the trace-exact cell meets
  (`constrain_cell_on_trace`).  Every operand/def/shape has a complete rule
  (`operand_constraints`, `def_constraints`); a rule's identity (top / no constraint)
  is the sound answer, never a gate or a bottom.  The forward relevance restriction
  (tag-only) is a forward-domain property, untouched.
- Keep the `set_stack_0` anchor tag; the fixpoint is a **Bourdoncle WTO fixpoint** (landed after the chunked design — the old "32-round chunks + `convergence_gap` + 64-chunk cap / `Fixpoint_not_converged` at 2048 rounds" text is STALE): WTO ordering stabilizes inner SCCs before outer, widening only at WTO heads after 10 warmup sweeps (landmark-directed: `Finite` extrapolates, `Zero` advances and joins, `Inf` standard-widens), always runs, no fallback (`cbat_vsa.ml:2791`). `not_implemented` always degrades to top with a logged warning.
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
  loose-hull — meet with circular hulls was over-approximating).  **The
  2026-08-30 consumption fixes (commit ②):** `observe_unsat_var`'s [is_upper]
  labels were INVERTED (the first arm — the set below a cap landmark — records
  [is_upper=true]), so the upper-extrapolation arm consumed nothing and the
  Finite path was a no-op; `translate_to` now translates by the observed
  GROWTH per traversal (dist_p − dist) × steps, CLAMPED at the landmark and at
  the current bound's outward side (a stale landmark can never narrow), with
  overflow → word_max ∞-arm; `add_smaller_dist` now PRESERVES the rotated
  history (`{entry with dist_p = existing.dist_p}`) — the re-acquisition after
  every advance had rebuilt the entry with `dist_p = None`, so `lm_calc_steps`
  returned `Zero forever (the Finite-never-fires bug); and the jcc decoder
  now also decodes `jne` (`~ZF` → NEQ) and `jz` (`ZF` → EQ) —
  `decoder_constraint`'s NEQ row is the exact two-piece `TOP−{c}` (the
  wrapped-[cur]-minus-point diff degenerates to a coarse hull, so the row is
  built from TOP and the exclusion happens at the meet), and
  `constrain_def_chain`'s INLINE-BinOp fallthrough routes the arrow-less
  record operand (`i − k` live, no `t :=` temp) through `refine_chain`'s
  MINUS row — the chain that lets a jne-guarded counter loop stabilize AT
  the landmark K (F1-NEQ: head max = K exactly).
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
- Env toggles: NONE in production (since 2026-09-03 — `HIKE_VSA_DEBUG`
  is deleted, and the build blocker bans every env read in src/; debug
  output is compiled in only under `--profile vsa-debug`). Test/probe
  code only: `HIKE_VSA_DIAG_BOTTOM=1` (precision_probe).  (`HIKE_VSA_RESTRICTION=0` exists ONLY in
  corpus_watch — precision_probe removed it (an OFF run crashes) — and it is
  DELETED by the restriction-removal spec.  `HIKE_VSA_ANCHOR=1` and the
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
- `semantic/run_semantic_opt.sh` → the OPTIMIZATION-SAFETY gate (2026-09-01): the
  same native-vs-lifted equivalence but with `opt-21 -O2` inserted between rename
  and llc — what a real consumer's optimizer does to the module must not change the
  lifted binary's behavior.  STRICT (exit 1, no allowlist, no exemptions); on
  failure it AUTO-BISECTS every single pass (`mem2reg sroa instcombine …`) and
  prints the full broken-by list (a `CRASH` marker = opt crashed on that pass,
  the fixpoint class).  Keeps `<name>_renamed.ll`/`<name>_opt.ll` as reproducible
  artifacts.  The pinned optimizer is `opt-21` (system LLVM 21; the emitter binding
  is 19.1.7 — the gate deliberately tests the modern consumer; NO FALLBACK if
  opt-21 is missing).  Born 23/32 on 2026-09-01; the poison-phi definedness fix
  (same day) flipped `mixed_fp_int` to **24/32** — the remaining 5 opt-induced
  failures are all instcombine-family (the model-SP-lane/push class — the
  optimizability program's next candidate: the call-push lane re-addressing)
  + the 3 pre-existing -O0 knowns (nested_struct, variadic, va_arg_vacopy,
  tickets T02/T03/T05 — listed, NOT exempted).  The red list is the work-list
  for the optimizability program.

## CURRENT VALIDATION STATE — refresh after EVERY change

**Last verified: 2026-09-06 EEST — CLEANUP-8 LANE (branch `cleanup-8`,
tickets 01+02+03+04+05 = commits `085f378`+`a124d97`+`858a33d`+`e518825`+`8281a8b`,
plus article-6 `39ffcb6` (frame_addr_alias linear via inverted target set;
A/B: gcc-12 alias 126→47ms) —
BATTERY GREEN, IR BYTE-IDENTICAL 35/35 on every ticket**

The cleanup-8 lane (spec: `.scratch/cleanup-8/spec.md`, grilling-settled
2026-09-06, 3 rounds): dead fields/params deleted (01), VLA detection runs
once and travels in `vsa_info.vla_alloc_tids` (02), ABI facts computed once
and threaded as values (03), DCE sweep is a worklist over contributor
counts (04 — A/B neutral, kept per review for the bounded-walk structure).

| gate | control (753601b) | cleanup-8 tip (e518825) |
|---|---|---|
| unit suite | ALL CBAT TESTS PASSED (467 ok) | **identical** ✅ |
| corpus emission | 35/35 rc=0 | **35/35 rc=0** ✅ |
| **IR byte-identity vs control** | — | **IDENTICAL 35/35** (incl. err files, on every ticket) ✅ |
| structural asserts | 172 pass / 3 fail (shape-d, pre-existing) | **identical** ✅ |
| semantics (all) | 30 PASS / 5 FAIL (same 5) | **identical** ✅ |
| optimization-safety (opt) | 30 PASS / 5 FAIL (same 5) | **identical** ✅ |
| semantics (8-bin) | 8/8 PASS | **8/8 PASS** ✅ |
| unmapped intrinsics | 0 fixtures / 26 gcc-12 pre-existing | **identical** ✅ |
| fixpoint non-convergence | 0 | **0** ✅ |

Measured side-notes (recorded in `.scratch/cleanup-8/spec.md`): the DCE
worklist A/B is neutral (ls 0.20→0.21s, du 0.35→0.37s, cksum 0.22→0.26s —
the census costs what the saved round cost); `Term.find`-per-pop
(0.33–0.51s/heavy sub, 5–14% corpus) is real but SHELVED as its own lane;
the int63 word substrate (`cbat_word.ml`, referee green 2.86M/0 mismatch)
is parallel-session in-flight work, untouched. Dead-by-measurement on this
lane: KB transport (0.001ms), stl model recompute (2ms), ABI-as-speed
(~1ms), `Sub.to_graph`×3 (0.3%, skipped by decision).

**Last verified: 2026-09-05 EEST — C8 WORKLIST DRIVER (branch `c8-worklist`,
tickets 01+02 = commits `9784985`+`c99777c`) — BATTERY GREEN, corpus IR
BYTE-IDENTICAL 32/32, grep −7%, and sub_4d2a CONVERGES (the C4 burn closes
as a side effect)**

The C8 lane (spec: `.scratch/c8-worklist/spec.md`, grilling-settled
2026-09-05, 4 rounds / 13 questions): the recursive WTO driver
(`stabilize_comps`/`stabilize_scc` — re-walk whole SCCs until quiet, 32–65%
of visits changing nothing: e350 1,521/2,334 useless) replaced by a
succ-seeded WTO-priority worklist (entry successors seeded; pop lowest WTO
position; full `process_vertex` per dequeue; enqueue Tid-successors on
change; the unchanged 6000-visit backstop). Dead blocks keep bottom
(`init_sol` default — sound, dead code). Widening: per-head K=10 warmup
(the landmark-ACQUISITION window — only the Inf arm can jump to TOP, and
only with no landmarks acquired; per-head is uniformly more conservative
than the global rule). C1 budget trigger moved per-SCC-entry → per-run
fixpoint-start (no stabilization episodes exist in a worklist; enforcement
half unchanged). F1-B2 amended to its behavioral core.

**Measured (interleaved A/B, 2 rounds each side, same binaries):**

| gate | control (`6a2d66b`) | worklist (`9784985`) |
|---|---|---|
| producer sort / grep | 13.43–13.45 / 21.82–22.10 s | 13.50–13.58 (**flat**) / 20.35–20.50 (**−7%**) |
| e350 visits / pops | 2,334 / 342,548 | **996 (−57%) / 236,032 (−31%)**; denote 3,698→1,621, join 4,666→1,992, widen 61→10 |
| 9f00 visits / pops | 975 / 135,210 | **441 (−55%) / 119,296 (−12%)** |
| **tag counts (927 subs)** | — | **926 IDENTICAL; 1 moved = sub_4d2a: 798 Unbounded → 609 real** (see below) |
| **tag kinds (all converged heavy subs)** | — | **IDENTICAL** (e350/8cb0/6b60/296a0/9f00/9570 byte-equal multisets) |
| **corpus IR** | — | **byte-identical 32/32** |
| corpus / check_allocas / semantic-all / semantic-opt / 8-bin | 32/32 · 160/0 · 30/2 · 30/2 · 8/8 | **identical to control on every gate** |

**The sub_4d2a verdict (the tag gate's investigate-before-landing clause,
resolved):** under the recursive driver the 544-node SCC burned all 6000
visits re-walking unchanged blocks and raised `Fixpoint_not_converged`
(degraded arm: 798 blanket-Unbounded tags, 4.79s). Under the worklist the
same 6000-visit backstop is spent on DISTINCT blocks — the fixpoint
COMPLETES (6.20s of real converging work) with 609 real tags (600 Ranges
incl. 360× Range(-1120,0), 83 Dead, 2 Infinite). Strict precision
IMPROVEMENT via convergence itself; ACCEPTED explicitly, tags re-baselined.
Sort stays flat overall because 4d2a now does useful work instead of
burning (this is the C4 class closing — a follow-up may tune it, not this
lane). Suite: 467 ok (incl. amended F1-B2 + untouched B1/B3/B4).
Artifacts: `/tmp/opencode/c8-ab/`.

**Last verified: 2026-09-05 EEST — C1 WALK-POP BUDGET (branch `c1-walk-budget`,
ticket 01 = commit `5ca6560`) — BATTERY GREEN, IR BYTE-IDENTICAL 35/35 (the
strongest possible outcome for this gate class), grep −4.8% / gcc-12 −2.5%**

The C1 lane (spec: `.scratch/c1-walk-budget/spec.md`, grilling-settled
2026-09-05): the deep backward walk (`refine_edge`) runs inline at every
conditional jump (ADR-0002) bounded by `~steps:256`; on the worst converged
subs 100% of walks truncate at the cap (grep sub_e350: 1,826 walks / 467k
pops / 74% of fixpoint wall post-merge). The budget BOUNDS that cost without
changing placement:

- **The cell:** `rc_walk_budget : int ref` in `Cbat_runctx.refine_ctx`
  (a ref field SHARES the cell across every `{rc with ...}` copy — the
  per-SCC semantics for free). `rc_out_edges` (per-block jmp counts) built
  ONCE in `mk_rctx` (the 73b756 per-visit-hashing lesson).
- **The recharge:** at EVERY `stabilize_scc` entry, `budget := 1024 × Σ
  (out-edges of the SCC's member blocks)` — one allowance per SCC
  stabilization; nested SCCs recharge their own at their own entry.
- **The enforcement (memo-first):** `Walk_memo.find` FIRST (a hit is free
  precision — never refused); on a miss the walk launches with
  `cap = max 1 (min 256 (max 0 !budget))`; the cell decrements per pop in the
  walk's `f` callback (VERIFIED: one graphlib `steps` iteration == one
  worklist pop — `graphlib_graph.ml:1402`, `iters` increments exactly when
  `step` pops `Set.min_elt works`); a budget-limited walk (cap < 256) does
  NOT `Walk_memo.add` (the empty-read-set trap); the zero-floor launches a
  1-pop walk (the guard block's own-def walk) — NEVER a skip, NEVER a gate
  (principles #2/#3: a shorter walk is the sound coarsening the 256 cap
  always was).
- **Instrumentation:** `bhits`/`psaved` on the STAGES line (vsa-debug only;
  the prod adapter no-ops).
- **DEAD, recorded (do not re-propose):** the seed-skip identity ("skip the
  walk when no Var seed's meet changed env") is UNSOUND — a no-op seed can
  still produce new CELL meets propagated backward through a Load def or a
  Load-valued phi (`constrain_cell_on_trace` inside the walk). Spec §1.

**Measured (A/B/A sandwich, 2 runs each side, interleaved):**

| gate | control (`e4b309c`) | budget (`5ca6560`) |
|---|---|---|
| producer sort / grep / gcc-12 | 8.23–8.25 / 13.98–14.01 / 32.60–32.67 s | 8.14–8.17 (**−1.1%**) / 13.24–13.39 (**−4.8%**) / 31.79–31.86 (**−2.5%**) |
| e350 walk lane | 2.43s / 1,826 walks / 467,456 pops | 2.08s / 1,613 walks / **342,548 pops (−26.7%)**, bhits 276, psaved 70,380 — arithmetic exact (1,337×256 + 276×1) |
| 9f00 walk lane | 155,648 pops | **135,210 pops (−13.1%)**, bhits 42, psaved 10,710 |
| **tag counts (all 2,421 subs)** | — | **IDENTICAL** (0 moved: sort 452, grep 475, gcc-12 1,494) |
| **tag kinds (every budget-bound sub)** | — | **IDENTICAL** (e350/8cb0/6b60/296a0/9f00/9570/4d2a: byte-equal kind multisets) |
| **IR** | — | **byte-identical 35/35** |
| corpus / check_allocas / semantic-all / 8-bin | 35/35 · 172/3 · 30/5 · 8/8 | **identical to control on every gate** |

The budget-limited walks' lost pops sat beyond what the TAG states consume —
full behavior preservation AND the speedup. C=1024 held; no raise needed.
Suite: 455 ok, output byte-identical to control. Artifacts:
`/tmp/opencode/c1-ab/`.

**Last verified: 2026-09-05 EEST — MERGE of `review3-removals` into
`perf-arch-10-work` (a9a1a8b, on 73b4756) — BATTERY GREEN, IR
BYTE-IDENTICAL 35/35, and a measured producer speedup**

The merge carried the stranded review-3 cleanup branch (built on fe8b411,
never merged into the restriction-removal line) into the current tip. The
eight commits: candidate 1 (delete the whole-callee recursion — `denote_call`,
the never-applied interprocedural fallback), candidate 3 (drop the discarded
live-solution derive in `refine_edge`), candidate 5 (interface-honesty batch:
`min_lo`, `emit_ctx.addr_bits`, `Relevance.is_sp`, `warn_once`, `is_void`/
`CallFunVoid`, the emitter `region_bytes` copy, info_join's dead arms),
candidate 4 (need_map folds `head_to_blocks` directly — one widening-point
walk, the duplicate forward Map deleted), candidate 6 (emitter cleanup:
`is_inline_fp_intrinsic`, dead params, `equal_krange`/`equal_vla_bound`
merged), candidate 9 (dead virtual temps at block exits: `live_in_of_sub` +
`AI.gc` + `MapLattice.filter_keys` — each transfer filtered by its target's
live-in before the join; machine regs exempt), candidate 12 parts 1+2 (the
never-None rctx option collapsed; `Cbat_runctx` split out of cbat_vsa.ml —
memo instantiations, flag_group, refine_ctx, flag/call facts, `mk_rctx`,
`ver_of` now live in the new module).

**Merge conflicts resolved:** (1) `hike.mli` — HEAD won (the branch's block
re-added `module Relevance`, deleted by ADR-0003 on this line); (2)
`hike_vsa_relevance.{ml,mli}` — deleted (HEAD won, ADR-0003); (3)
`cbat_vsa.ml` ×4 — the `Cbat_runctx`-qualified types + `rctx`-threading
(branch shape) won over HEAD's inline types/`Option.value` plumbing, but the
branch's `?refineable` param was DROPPED (rr-03 deleted it on this line) and
the branch's `denote_call` body was DELETED (candidate 1's whole point);
(4) `cbat_runctx.ml` — the branch's `rc_all_tagged` field + its
`Term.has_attr Utils.relevant` construction REMOVED (relevance machinery,
ADR-0003); `rc_live_in`/`AI.gc` KEPT (candidate 9's payload).

| Gate | Result |
|---|---|
| unit suite | **ALL CBAT TESTS PASSED** (`dune runtest`, incl. T01 chain/D0-D5/LM fixtures) ✅ |
| corpus emission | **35/35 rc=0** (32 fixtures + sort/grep/gcc-12) ✅ |
| **IR byte-identity vs 73b4756 control** | **IDENTICAL 35/35** ✅ |
| structural asserts | **fixtures 172 pass/0 fail; 3 pre-existing fails on gcc-12/grep/sort (shape-rule d) — IDENTICAL ON CONTROL** ✅ |
| semantics (all) | **30 PASS, 5 FAIL** — the same 5 on control (gcc-12/grep/sort harness-class + T02/T03) ✅ |
| semantics (8-bin) | **8/8 PASS** ✅ |
| **producer time (subtimes, 2 runs each)** | **sort 10.5–15.2s → 8.2–8.4s; grep 17.1–26.4s → 14.0–14.4s; gcc-12 45.6–61.7s → 32.9–33.1s** — −18…−46% (post-merge runs within 1.5% of each other: real, stable) ✅ |
| stage counters (grep sub_e350) | denote 5.8→3.5s, join 0.57→0.17s, walk 4.3→2.6s, minor-words 1.17B→1.09B — the live-in GC shrinks every downstream join/equal ✅ |

NOTE: the semantic-opt gate is subsumed by IR byte-identity (identical IR ⇒
identical optimized behavior). The 3 check_allocas shape-d fails and the
3 semantic fails on the real PIE binaries are PRE-EXISTING on the control
(recorded, not introduced). Artifacts: `/tmp/opencode/merge-validation/`.

**Last verified: 2026-09-03 EEST — comment concision pass (83 files,
+2175/−6394, comments only) — BATTERY GREEN, identical behavior**

Every code comment rewritten to the minimum: what the current code does,
present tense, 1–2 lines. All history deleted (phases, ora-/ticket refs,
dates, removed/moved notes, port deltas, incident references, doc-path
pointers, banner numbering). Verified comment-only three ways: (1) full
`dune build` green (exercises cppo, the instrumentation blocker, all
probes); (2) comment-stripped sources diffed against HEAD — zero
non-comment changes (modulo heredoc false positives, cleared
file-by-file); (3) test output byte-identical: cbat 467/467 names match
(40 stubbed = 40, 0 FAIL), relevance 26/26. Full emission battery rerun:
corpus 32/32 rc=0, check_allocas 160/0, semantic-all 30/2/0,
semantic-opt 30/2/0 (identical — opt-induced class empty), 0 unmapped
intrinsics. Gated `#ifdef VSA_DEBUG` regions verified byte-identical.

Fixed 2026-09-03 (review #2, candidate N1): the `promoted_words` field was
NEVER gone (verified in the OCaml 5.3 toplevel — it exists and works). The
real mechanism: `src/cbat_vsa/dune` copied the adapter verbatim with no cppo
step, so the trailing `#ifdef VSA_DEBUG` parsed as a method call on the
PRECEDING expression — `(!gc0).Gc.promoted_words #ifdef …` — hence "not an
object; has type float" pointing at line 69, three lines above the guard.
Fix: the cppo stanza mirrored into `src/cbat_vsa/dune`'s `cbat_vsa` library
(cppo+ppx-jane replaces `pps ppx_bap`; driver-set equivalence verified
against every deriving clause). Verified: vsa-debug build rc=0,
vsa_debug.exe/wbig_diag.exe build and run, default profile rc=0 with the
report body compiled out (0 forensics-string hits), `dune runtest` green,
corpus 32/32 rc=0 and IR byte-identical 32/32 to the pre-fix control
emission, check_allocas 160/0, 0 unmapped intrinsics.

**Last verified: 2026-09-03 EEST (morning) — MAIN @ 87c9b86 — THE TRIPLE
MERGE: the optimizability program (mem-fission, opt gate, FP-table fix,
arch-c1c6) + the 2026-09-02 architecture-review program (candidates
#3/#2/#5/#1: mk_rctx, the Cbat_memo module, the Cbat_wto module, the
cbat_extraction submodule, the hike_stack_model split, ADR 0005) + the
diag-channel regime (Hike_diag, cppo compile-out, the build blocker,
the DUNE-BUILT PLUGIN) — BATTERY GREEN, IR BYTE-IDENTICAL to a fresh
main control 32/32 (the only err_ diffs: the Q11 progress-print
deletions — the merged tree is cleaner), 30/2 at BOTH -O0 and opt -O2,
160/0 allocas, 0 unmapped intrinsics, ZERO env reads**

The merge resolution record (both commits' messages carry the full
detail): the fission body + the review topology; C2 + empty_vsa_info
with vla_bounds unified on the MAP; the stages debug adapter's report
behind #ifdef VSA_DEBUG (the adapter the blocker never met); the
plugin-clash postmortem (the Hashtbl.add_exn crash = the legacy
bapbundle zip + the dune plugin both installed — fixed by the regime's
recipe: `bapbundle remove hike` then `dune build @install && dune
install`). The INHERITED-STATE note below is RESOLVED (main's merge
completed; this IS it).

**The arc (the grilling-settled design, 17 questions, one session):**
the user directive "the instrumentation should not be compiled in the
production binary" restated principle #6 as COMPILE-TIME ELIMINATION.
Mechanism facts established by experiment first: ppx_optcomp is DEAD
for this (no `-D`; `[%import]` fails in dune's ppx sandbox), cppo (in
the switch) works end-to-end (`#ifdef VSA_DEBUG` lines, `-D` keyed by
dune's `%{profile}` through `src/cppo_preprocess.sh`), and ppx-jane IS
the old `pps ppx_bap` driver (it regenerates `[@@deriving equal]`'s
`equal_vsa_kind` — cppo must run BEFORE it, never replace it).

- **`Hike_diag` (src/hike_diag.ml) is the ONE production channel.**
  `Hike_diag.warn` prepends the `hike:` prefix `run_corpus.sh` greps.
  Migrated in: the section-not-found warning (hike.ml), the Unbounded
  guarded warning, the unmapped-intrinsic warning, both undef-read
  warnings (bil2llvm), the not-converged and 100%-invariant-gap warnings
  (hike_vsa).  The cbat_vsa `not_implemented` raw-stderr duplicate is
  DELETED (BAP's Event.Log keeps it; nothing grepped the copy — corpus
  err_*.txt carries only guarded/undef-read lines, verified).
- **Deleted as noise (per Q11 triage, confirmed):** 12 hike.ml
  section/symbol progress prints, 3 bil2llvm per-sub traces, the per-hit
  `create_load DYN addr=` dump, and ALL 6 `HIKE_VSA_DEBUG` env gates.
- **Gated behind `#ifdef VSA_DEBUG` (the valuable forensics):** the
  region-NOT-convertible dump + member-NOT-direct print (stl), the
  create_static_mem_access fallback print (bil2llvm), the vsa/stl
  tag-count prints (hike.ml, incl. the vsa-guard skip note).
- **The blocker** (`src/check_instrumentation.sh`, aliases `all` +
  `install`): zero-exemption env-read ban + comment-aware direct-print
  ban; VERIFIED red (injected violation → `dune build` rc=1, both rules
  fire) and green (rc=0, `@install` too).
- **Cheap debug builds:** `--build-dir _build-debug --profile vsa-debug`
  (measured thrash without it: full 10-22s rebuild EVERY switch, both
  directions, zero shared cache).
- **The plugin is DUNE-BUILT now** (user directive): `(plugin (name
  hike) (libraries hike) (site (bap-common plugins)))` in src/dune,
  `(using dune_site 0.1)` in dune-project.  bapbuild/bapbundle RETIRED
  — bapbuild's own ocamlfind pipeline could not see the cppo stanza (a
  raw `#ifdef` reached the parser: Syntax error at hike.ml:662).  The
  `llvm` package ships no `llvm.cmxs`/META;
  `src/backfill_llvm_cmxs.sh` builds it (bapbundle's recipe, byte-
  identical 501008 bytes) and backfills the switch; the legacy
  `hike.plugin` zip must be removed (`bapbundle remove hike`) or bap
  loads both and dies (`Hashtbl.add_exn ... hike`).
- **Provenance:** `src/record_provenance.sh` (run after `dune install`)
  writes `hike.cmxs.provenance` — tree, git describe, src sha16, bundle
  sha16 — for the battery to verify; mtime checking CANNOT catch a
  plugin from a different tree (measured 2026-09-02: identical sources,
  22 poison phis, mtime warning silent, corpus rc=0).

| Gate | Result |
|---|---|
| unit suite | **467 ok / 0 xfail / 0 XPASS / 0 FAIL** (`ALL CBAT TESTS PASSED` both suites; the strict harness passes OUTRIGHT on this tree) |
| corpus emission | **32/32 rc=0** |
| **IR byte-identity vs main 40955da control** | **IDENTICAL 32/32** (the strongest control: every deletion/gating/channel migration changed ZERO emitted bytes) |
| structural asserts | **160 passed, 0 failed** |
| semantics (all) | **30 PASS, 2 FAIL** (va_arg_vacopy + variadic, T02/T03) |
| optimization-safety (opt) | **30 PASS, 2 FAIL** — identical to -O0 (the opt-induced class is EMPTY) |
| semantics (8-bin) | **8/8 PASS** (this branch predates the gate-collapse on `battery-merged`) |
| unmapped intrinsics | **0** |
| probes | precision_probe factorial/alloca_vla + corpus_watch array_local — **PASS, 0 crashes** |
| blocker red path | injected `Sys.getenv_opt` violation → `dune build` **rc=1**, both rules fire; clean → rc=0 |
| compile-out proof | production `hike.pp.ml`/`hike_stack_to_locals.pp.ml` grep the forensics strings → **0 hits**; `_build-debug` copies → **1 hit each** |

INHERITED-STATE NOTE (2026-09-03, RESOLVED — main @ 87c9b86 completed the
merge; this entry is now main's record): the mid-merge conflict in
`test_cbat/test_cbat.ml` is reconciled. This branch also predates `battery-merged`
(2026-09-02: the battery driver + the three-gate semantic collapse) —
the two branches touch DISJOINT files (src/ + dune vs test_cbat/ +
scripts/) and should merge cleanly.

**Directive (NON-NEGOTIABLE):** after every change to `src/` or `src/cbat_vsa/`, re-run
ALL gates below and rewrite this section with fresh numbers and a fresh timestamp. An
AGENTS.md whose "current state" disagrees with the tree is a doc BUG — the next session
will trust these numbers to distinguish its own regressions from inherited ones (the
2026-08-26 rename_intrinsics incident below is exactly that failure mode).

**Last verified: 2026-08-31 EEST (early morning) — the ABI module + debug harness
restoration — FULL GATE BATTERY GREEN, identical semantics**

**The ABI refactor (this session, on the KB-fix tree, commit-by-commit green):
one `Hike_abi` library (unwrapped, bottom of the lattice: hike_abi ←
cbat_vsa_domain ← cbat_vsa ← hike) owns the `abi` record (sp/fp,
int/vector param regs, return regs, callee-saved), the `x86_64_sysv` value,
the var predicates (`is_sp`/`is_fp`/`is_stack_reg`/`is_preserved`), and the
ex-Targetutils target-derived registers (`sp`/`fp`/`pc`/`addr_size_bits`/
`resolve_alias`/regs) + `of_target`. All consumers migrated: hike.ml,
bil2llvm (`cast_source_width`/`degraded_geometry`/`degraded_dims` now take
`~abi`, threaded from the emit ctx), hike_stack_to_locals, hike_dce,
convutils, hike_vsa_relevance, and cbat_vsa's 5 inline x86 sites (the call
abstraction's rsp/escape/preserved lists, the `constrain_cell` RSP test,
`prove_nonneg`'s stack anchor). Zero `"RSP"`/`"RBP"` strings left in src/
outside `hike_abi/hike_abi.ml`. GOTCHA (cost two failed plugin loads): the
library/module must NOT be named `abi`/`Abi` — BAP's own core `abi` plugin
(module `Abi`) is dynlinked into every bap process and wins the name
("interface mismatch on Abi"); the library is `hike_abi`, the module
`Hike_abi`, exported to consumers as `Hike.Abi` via a plain alias.**

**The KB-store fix (prior session, on the Finding-1 tree): the vsa-info KB
slot's silent drop is gone.** `Hike_kb`'s slot domain is now MAP EXTENSION
(order) / MAP UNION (join): a provide that adds subs the map lacks is a
monotone update, a re-provide of the same map is idempotent, and two
DIFFERENT infos for one sub raise a loud `Toplevel.Conflict` (the
`Vsa_info_conflict` extension + `KB.Conflict.register_printer` — the KB's
own `Non_monotonic_update` machinery, not a hand-rolled guard). Two dead
limbs deleted: the write-only `vsa_sol_tbl` Hashtbl (`vsa_sol` /
`provide_sol` / `add_sol` — one writer, zero readers repo-wide; every
sub's fixpoint solution was retained process-globally for nothing) and the
always-`[]` `Convutils.vsa_info.call_stack_args` field (the M2 removal —
record, the `call_stack_args_of_sub` function, all 7 record literals).
The vsa pass's re-entrancy guard (`hike.ml`) STAYS as an
idempotence/perf guard (its stale "M2 (ADR 0004)" comment rewritten — the
join domain makes a second run's provide idempotent-or-conflict, so the
skip is pure fixpoint-cost avoidance, NOT a soundness gate). Docs fixed to
the join-domain contract: the `hike.mli` `Kb` doc (the write-once caveat
is gone), the header's self-contradictory "Deliberately NOT exported:
[Hike_kb]" sentence ([Hike_kb] IS exported as `module Kb`), and the A4
test comment (the fixtures still BORROW C1's entry — providing their own
info under C1's tid would now conflict; minimal-change doctrine keeps the
borrowing). Per the user's directive, NO unit tests were added for the
join/order machinery itself — BAP's KB is upstream-tested; the domain is
exercised end-to-end by the corpus battery. Net: ~+85/−53 lines.

**Last verified: 2026-09-02 EEST (late) — MAIN @ c484e13 — the FP-intrinsic
table regression FIXED — BATTERY GREEN, 30/2 at BOTH -O0 and opt -O2, no gate
moved**

**The native_fp_op merge regression is FIXED (commit c484e13, this session).**
The merge `a7b7a6a` silently dropped 11 of the 26 rows of
[Bil2llvm.native_fp_op] — a both-sides-changed drop. It took the BRANCH
parent's table and then lost even the branch's own forder/cast_* rows,
leaving 15 rows producing only FMUL/FADD/FSUB/FDIV/FREM. Consequence: 5 of the
10 [native_fp] constructors were never built, so the SFLOAT/SINT/FORDER/ISNAN/
FHLT arms of [create_native_fp_call] (~103 lines) were unreachable, and every
cvtsi2sd/cvttsd2si, every COMISS/COMISD compare and hlt degraded to
`hike: guarded: unmapped intrinsic call` with POISON result lanes. Measured:
**9 warnings** across mixed_fp_int / union_overlap / va_arg_mixed, and
mixed_fp_int emitted **0** native sitofp/uitofp where the pre-merge tree
emitted 5 (replaced by 5 soft-float calls). Fixed by restoring all 26 rows
from the MAINLINE parent `cef072a`, which is authoritative (it carries
`b7b2dae`'s is_nan + unsuffixed-forder rows, and HEAD's call arms are already
the mainline's TYPE-DERIVED versions taking `~abi`). Now: **0** unmapped
intrinsics, 5 native sitofp, 0 soft-float calls, 29 of 32 binaries
byte-identical (only the 3 affected ones changed).
LESSON (the reason this survived a recorded-green battery): the degradation
emits a CORRECT soft-float sub, so stdout stayed byte-identical, and the 3
affected binaries are NOT in the 8-bin oracle — **a "surviving diagnostic" is
not a passing gate.** Grep the emissions for `unmapped intrinsic` when
changing the FP-intrinsic table.
**Last verified: 2026-09-02 EEST (final) — MERGED TO MAIN (82311d7, the
arch C1+C6+C4+C2 fast-forward) + candidate 3 SKIPPED BY MEASUREMENT —
BATTERY GREEN ON MAIN, 490 checks, IR byte-identical to BOTH the branch
emission AND the pre-merge main control, 32/32**

**Candidate 3 (the shape_of_addr linear-scan + mapper-hoisting item)
WILL NOT BE DONE (user decision, 2026-09-02; the measurement that
justified it — probe `stl_timer`, deleted after the run, never
committed):**
- **The perf pitch is DEAD.** stl is 0-4ms/binary over the corpus, 35ms
  (sort, 452 subs) / 45ms (grep, 475) / 140ms (gcc-12, 1494 subs) on
  real PIE binaries — against offsets lanes of 2.5-21s. stl+dce ≈ 1-2%
  of the per-binary time; a 10x speedup saves ~100ms of 21s.
- **What the census DID find (recorded here so a future review does not
  re-run it):** duplicate addresses are the COMMON case — 60-70% of
  tagged defs share an Exp.equal address with another def (grep
  6022/8768, gcc-12 19559/28400). [shape_of_addr]'s assoc-list
  find_map returns the FIRST match in the consed list = the LAST def in
  walk order — a silent LAST-WINS rule over potentially divergent tags
  (two same-address defs in different blocks can carry different
  regions/shapes). The corpus binaries' duplicates happen to AGREE, so
  the behavior is correct-but-accidental; no unit fixture pins it. If a
  future same-address divergence bug surfaces, the pin to write is:
  two Exp.equal-address defs, divergent tags (one singleton-Slot, one
  interval-Region), assert the later def's shape serves both.
- **[merge_loop] (regions_of_sub) is the actual measurable hot spot**
  (16.7ms max-per-sub on grep, 703 items — vs stl's 2.9ms) but its
  component order DETERMINES the region ids (stack_rN names): any
  algorithm change (e.g. sort-and-sweep) renumbers regions corpus-wide
  and breaks IR byte-identity — a deliberate re-baseline session, never
  a rider.
- BAP facts the measurement established (probe-verified):
  [Exp.hash] + [Exp.compare] both exist (Regular.S); structurally-equal
  exps are NOT physically equal (no lifter hash-consing); Filliâtre's
  hashcons lib is already linked into the plugin if ever needed.

**Merged to main (fast-forward, no conflicts; main's parallel-session
untracked scratch untouched): C1 (the fission name is ONE fact) + C6
(comment debt, every reference names a real thing) + C4 (the DCE pass
gets a real interface — hike_dce.mli, Hike.Dce, total ABI lane, 6
fixture tests D0-D5) + C2 (vsa_info IS the precomputed view — the
offsets/k_ranges fields are the Tid maps). The installed plugin is
MAIN's build (rebuilt + reinstalled post-merge).**

**Last verified: 2026-09-02 EEST (late night) — arch C1+C6+C4+C2 on branch
`arch-c1c6` (C2 = commit 243ef22) — BATTERY GREEN, 490 checks, IR
BYTE-IDENTICAL to main 32/32**

**C2 (243ef22): `vsa_info` IS the precomputed view.** The record's
`offsets`/`k_ranges` fields ARE the per-def Tid maps now (Tid → kind,
Tid → (klo,khi)), built ONCE at the producer — the record stops being
"raw lists + know how to index them". Deleted: five consumer folds in
stl, the emitter's per-def O(n) `find_def_tag` scan (ONE map find per
stack access now), hike.ml's `has_positive`, and the three probes'
`kind_of` folds. Constructors: `Convutils.mk_vsa_info` (the one
list-taking fold — fixtures/probes) + `mk_vsa_info_maps` (the producer
tail). `equal_vsa_info` is hand-written (maps); entry ORDER left
equality with the lists — and the tree's ONE order dependence (the A4
test's positional `List.nth` borrow over C1's walk-order offsets) died
with it (sorted-tid keys now). The record STAYS the KB slot's per-sub
value — that is what vsa_info is FOR (the join/conflict domain); no
second view type. Gates: 490 ok + 6 xfail (identical count); corpus
32/32 rc=0; unmapped intrinsics 0; check_allocas 160/0; semantic
30/2, 30/2, 8/8 (T02/T03 only); probes 10/10; IR byte-identical to
main a5680df 32/32.

**Last verified: 2026-09-02 EEST (night) — arch C1+C6+C4 on branch `arch-c1c6`
(worktree `/home/tovpr/backup/hike-arch`; C4 = commit 8743bb9, on the
a5680df-rebased C1+C6 tree) — BATTERY GREEN, 490 checks, IR
BYTE-IDENTICAL to main 32/32, the FP-table fix (c484e13) carried**

**C4 (8743bb9): the DCE pass gets a real interface.** `hike_dce` had 16
visible lets, no `.mli`, ZERO tests, and was untestable BY CONSTRUCTION
(every ABI query went through `Abi.sp`/`of_target`, which RAISE on
`Theory.Target.unknown` — the fixture target). Now: `hike_dce.mli`
exports `dce` ALONE (exported through the seam as `Hike.Dce` — the
phantom `is_precise_sub` doc ref in hike.mli is fixed); the ABI lane is
TOTAL (`abi_of`/`sp_of` fall back to the x86_64 SysV record, the stl
`fp_of` pattern); duplicates deleted (`is_ret_reg` → `Abi.is_return_reg`;
the `intrinsic:` prefix is ONE fact, `Convutils.is_intrinsic_name`,
serving dce + bil2llvm's call dispatch + hike.ml's free-var filter);
`sp_value_exp` STAYS (not a duplicate of stl's `exp_contains_sp` —
different Load/Store semantics, now documented). Six fixture tests
through the new seam (D0-D5: totality+sweep, the epilogue rewrite with
negative controls, the always-keeps, the two-tier region-mem rule, the
precise-path SP-erasure with the production-shaped control, the
`Sub.intrinsic` passthrough). TEST-FIXTURE GOTCHAs recorded: a fission
load whose RESULT is unused dies itself and UN-ROOTS the chain (the
documented cascade — root it with a jmp cond read); a non-precise
`hike_stack` def needs the PRODUCTION use shape (the incoming-arg load
at `[hike_stack + k]`) to survive the sweep. Gates: **490 ok** + 6 xfail
(484 + 6 new); corpus 32/32 rc=0; unmapped intrinsics 0; check_allocas
160/0; semantic 30/2, 30/2, 8/8 (the T02/T03 knowns only); probes 10/10
+ all debug executables build; **IR byte-identical to main a5680df,
32/32**. (The plugin-pointer note is superseded: post-merge, the
installed plugin is MAIN's build.)

**Last verified: 2026-09-02 EEST (evening) — arch C1+C6 on branch `arch-c1c6`
(worktree `/home/tovpr/backup/hike-arch`; rebased onto main a5680df after the
c484e13 FP-table fix — the IR-identity control was against a217289-era main,
PRE-fix, so the 3 FP-affected binaries' IR is expected to change with the
rebase) — BATTERY GREEN on the pre-rebase tree**

The architecture-review follow-ups (candidates 1 + 6 of the review at
`/tmp/opencode/architecture-review-20260902-051945.html`), two commits:

- **C1 (e85ed8d): the fission name is ONE fact.** The `stack_rN_mem` /
  `stack_rN_base` naming convention had three hand-typed string parsers
  (`hike_dce.is_region_mem`, `bil2llvm.is_region_mem_exp`, and the
  φ-lane's inline prefix/suffix test); `Hike_stack_to_locals` now exports
  `is_region_mem` / `is_region_base` next to the producers, and every
  consumer imports them. The predicates also joined `hike.mli`'s
  `Stack_to_locals` signature (the convention is constructible and
  recognizable through the library seam — tests can build fission vars
  one way). Grammar deliberately unchanged — pure single-sourcing.
- **C6 (3fa2257): comment debt + dead code.** Nine stale references fixed
  (the nonexistent "ADR 0004" ×3, the never-implemented
  `escaped_addr_tids`, the wrong `abi_visibility_of` pipeline claim, the
  deleted `has_frame_ptr`/`region_split_plan` refs in dce + check_allocas,
  the Q1/A-Q2-Q5 dialogue labels, BNF1, stage_timer's wrong claim that
  stl/dce run inside `offsets_of_sub`); dead `bil2llvm.def_tags_of` +
  `find_def_k` deleted; test R12-5/6/7 now asserts through the REAL
  seam (`Stl.split_plan` on a BIL fixture + derived `equal_split_plan`)
  instead of re-implementing the covered/disjoint rule locally.

Verification: `dune runtest --force` **484 ok + 6 xfail, ALL PASSED**
(484 = main's count; the R12-5/6/7 rewrite kept the count); corpus
**32/32 rc=0**; check_allocas **160/0**; semantic-all **30 PASS / 2
FAIL** (va_arg_vacopy + variadic, T02/T03); opt gate **30/2 identical**
(opt-induced class still empty); 8-bin **8/8**; precision_probe +
corpus_watch spot-checks **0 crashes**; **IR byte-identical to a fresh
control emission from unmodified main, 32/32** (the `emissions/fission`
reference is PRE-MERGE and unusable as an identity oracle — its
SP-restore phi names differ; emit a fresh main control instead).
NOTE: the installed plugin currently points at the arch-c1c6 build —
rebuild+reinstall when switching back to main.


**Mem-fission (this session, commits 6cc2c86 + 499bb36 on finding1-stack-plan):
the storage decision lives in the BIL, and DCE deletes dead stores
naturally.**  The architecture arc: the Candidate-3 model-clean WIP (the
positional push deletions + their compensations — the mov rewrite, the
VSA retaddr flag, the sp-8 hike_stack compensation, the restore
tombstone) was REVERTED in full (its 3 regressions — many_args/sret_big/
struct_by_value — were all one class: the store/load cell-split, one def
classified differently across blocks, machine-proven in IR and asm);
the superseding design (.scratch/mem-fission/research.md — 565 cited
lines, the BIL-multi-mem feasibility against BAP's own sources) keeps
the BIL MACHINE-ACCURATE end-to-end and adds three mechanisms:
(1) stack_to_locals fissions every CONVERTIBLE ranged region to a
per-region mem var (`region_mem id` = `stack_rN_mem`) AND rewrites the
address base (`region_base id` = `stack_rN_base`, entry-bound to the
region alloca's cell-0): `mem[RBP + i*4 - 0x70]` becomes
`Load(stack_rN_mem, stack_rN_base + i*4 - 0x70)` — BOTH operands name
the region, the cell-split class closes BY CONSTRUCTION.  Singletons
keep the slot-var degenerate (bit-identical).  The ONE positional rule
(`last_push_tids_of`: the call block's last stack def = the retaddr
push) exempts the dead push cell from ABI visibility, so it fissions
into a never-loaded region — reusing the tail-set's own walk, no new
classifier; (2) hike_dce two-tier: a region mem var's defs survive iff
the var has a LOAD-ROOT (Load-side mem uses only; Store-side uses never
count — the self-keep the fission deletes); the lifter's `mem` keeps
the always-keep (ABI/external/outgoing traffic); (3) bil2llvm's
name-keyed dispatch: `stack_rN_mem` operands route through the fission
arms, the region base binds to the alloca cell-0 at create_sub, and the
definedness closure's name rule threads the base vars.  Measured (base
-> fission): retaddr push stores 112->92 (fizzbuzz 8->1, mixed_fp_int
2->0, fptr_table 2->0, landmark_loop_1000 1->0, rmw_oob 1->0,
array_local 1->0, deep_recursion 4->2, setjmp_longjmp 10->7,
setjmp_loop 4->3); inttoptr 844->802 (landmark_loop_1000 3->0,
deep_recursion 9->4, fizzbuzz 12->3); **opt gate 24->26** (fizzbuzz +
fptr_table FLIPPED GREEN — the dead push stores no longer alias the
caller's frame under instcombine).  GOTCHAs recorded: the base vars
need phi lanes (Candidate 2's definedness closure would otherwise
filter them — the name rule admits them); region mems must NOT be
zero-initialized (their cells ride the alloca's original bytes).

| Gate | Command | Current result |
|---|---|---|
| unit suite | `dune runtest --force` | **480 checks, 0 FAIL** (`ALL CBAT TESTS PASSED`) ✅ |
| corpus emission | `bash scripts/run_corpus.sh <corpus> <emissions/fission>` | **32/32 rc=0** ✅ |
| **unmapped FP intrinsics** | `grep -rh "unmapped intrinsic" <emissions>/*.txt` | **0** ✅ (was **9** before c484e13 — the merge regression; see below) |
| structural asserts | `bash scripts/check_allocas.sh <emissions/fission>` | **160 passed, 0 failed** ✅ |
| semantics (all) | `bash scripts/semantic/run_semantic_all.sh ...` | **30 PASS, 2 FAIL** ✅ (the merged tree beats both parents: mainline's fixes + the fission recovered `nested_struct` — a former -O0 known; the remaining 2 = va_arg_vacopy + variadic, tickets T02/T03) |
| **optimization-safety** | `bash scripts/semantic/run_semantic_opt.sh ...` | **30 PASS, 2 FAIL** ✅ (identical to -O0 — the opt-induced class is EMPTY on the merged tree: the fission's dead-push deletion + mainline's edge-keyed restore together close the SP-lane classes; the remaining 2 are the -O0 knowns, failing identically at both levels) |
| semantics (8-bin) | `bash scripts/semantic/run_semantic.sh ...` | **8/8 PASS** ✅ |
| probes | precision_probe spot-checks (factorial, rec_struct, array_local, variadic, alloca_vla) | **PASS, 0 crashes** ✅ |
| FP micro-suite | fm2/fm4/fm6/fmc8 native-vs-lifted | NOT RE-RUN this session |
| coreutils PIE (103) | `coreutils_pipeline.sh` lift+test | NOT RE-RUN this session |

All numbers above are from the tree at **c484e13** (main), re-measured this
session against `/tmp/corpus` (32 binaries, built 2026-09-01). The two semantic
gates were run against BOTH the pre-fix and post-fix emissions: **30 PASS /
2 FAIL with the SAME two binaries** either way, so c484e13 fixes a real
regression without moving any gate. Emissions: `/tmp/opencode/em_before`
(pre-fix), `/tmp/opencode/em_after` (post-fix, 29/32 byte-identical to
before).

**Reference artifacts (durable — /tmp wiped twice):** worktree
`/home/tovpr/backup/hike-finding1` (branch finding1-stack-plan); corpus
`/home/tovpr/backup/hike-corpus`; emissions `/home/tovpr/backup/emissions/{base,fission}`;
semantic outputs `/home/tovpr/backup/sem-*`.

**The surviving branch program (finding1-stack-plan):** ee916b1 the opt
gate → d599193 the poison-phi definedness fix (689→0 poison phis, opt
gate 23→24) → 6cc2c86 the model-clean revert + the native_fp_op suffix
rows (the fresh corpus's sse-binary names) → 499bb36 mem-fission (this
commit).  The 3 -O0 knowns (nested_struct, va_arg_vacopy, variadic —
T02/T03/T05) are unchanged.  The natural follow-ups: the remaining
opt-induced classes (runtime-addressed lanes), and stack-args-as-params
(the many_args family's push-only tails keep the conservative outgoing
block by design until then).

**Finding 1 landed (uncommitted, on the 2026-08-30 ② tree + this tree's
in-flight `hike.mli` work): the stack model decision now has ONE producer.**
`Hike_stack_to_locals.split_plan` owns it; `regions_of_sub`'s per-region
`convertible` flag carries the escape gate; the decision travels in the new
`Convutils.vsa_info.stack_plan` field; and `Hike_stack_to_locals`,
`Hike_dce` and `Bil2llvm` are its three CONSUMERS. `Bil2llvm.region_split_
plan` is DELETED (its whole-sub rules — degraded, escape, unbounded access,
VLA overlap, inside/disjoint tag coverage, region size — moved to the
producer); the emitter's `create_def` collapsed from nine near-duplicate arms
(a precise arm + a verbatim non-precise copy) to one shared `mem_access`
dispatcher; `hike_dce` no longer imports the emitter (`is_precise_sub` reads
`stack_plan`); the two `is_abi_visible` copies are now one rule the emitter
calls; and `hike.ml`'s second `regions_of_sub` call (which overwrote the
first) is gone — regions are computed once per sub. Net: **−318 lines**.

Two unification notes for the next reader:
- The escape rule is **per-region**, NOT whole-sub — `stack_to_locals`
  consults `convertible` even on the fallback path, so moving the escape
  gate into `split_plan` alone made `rec_struct` regress (28/32 → fixed
  by keeping it in `regions_of_sub`, to which it is now passed as
  `~frame_escaped`).
- The two escape analyses that used to disagree (`sp_escaped` here vs the
  emitter's `frame_ptr_value_def`/`has_frame_ptr`) are unified as
  `frame_escapes` = `sp_escaped || frame_addr_alias`. The alias half is
  NEW coverage (the bare-copy `v := RSP; t := mem[v]` class the emitter's
  generalized predicate caught and `sp_escaped` did not) — that is why
  5 binaries now convert MORE slots (fewer `poison` phis) while all
  semantics stay byte-identical.

**Gate results: identical to the 2026-08-30 baseline (29/3), and the 8/8
oracle passes.** Emitted IR differs from `/tmp/heritage_lmC` on 8 of 32
binaries, ALL in the "fewer poison phis / more real slot stores" direction
(strictly more precise), with identical `stack_r` alloca counts (7).
Production `Sys.getenv` debug gates dropped 16 → 6.


This second session of the day landed the landmark CONSUMPTION fixes on top of
the mapD tree (`3ebd805` = commit ①, the stack-to-locals rework, itself on
`46e1207`/`62a466a`). ② = the consumption-fix delta as COMMITTED `6dd9cce`
(on `5ae223b`; tree clean — the "uncommitted" description in earlier edits
was STALE). The Q1-C/Q2-B/Q3-C/Q4-A
grilling-settled design: the threshold ladder (`Cbat_thresholds` + all
`widen_join_threshold` mirrors) DELETED, the Inf arm = plain `AI.widen_join`,
the Zero arm = plain join, per-arm advance/clear + the stability check (see
the widening section above for the full fix list — the inverted [is_upper]
labels, the growth-clamped `translate_to`, the `dist_p` history-carry, the
jne/jz decoder arms, the exact NEQ row, the INLINE-cmp backward walk).
**F1-NEQ passes the strict acceptance test: `max == K` exactly (head =
[0..100])** — the record of an earlier AGENTS.md edit today describing the
mapD state as current (with "relaxed assertions") was STALE: the tree
verifiably carries ② (`git diff` = the ② delta; `dune runtest` 0-fail with the
strict test; `/tmp/heritage_lmC` emitted today 18:08).  The mapD work (commit
①) is described below; its gate numbers are superseded by this table.

The prior session's record (commit ① `3ebd805` — the stack-to-locals rework):

1. **THE MAP SOLUTION (`src/hike_stack_to_locals.ml`)**: the conversion is
   now ONE [Exp.mapper] over the def rhs mapping ONLY the matching
   load/store nodes (the address-keyed `local_of_addr`); ALL enclosing
   structure (casts, binops, ites, lets) is preserved and re-emitted by the
   ordinary emitter — the emitter's [create_cast]/[coerce_to_same_type]
   produce the widening at exactly the BIL type boundaries (no emitter-side
   promotion). The def-lhs rebind ([mem := mem with [addr] <- data] becomes
   [slot := data] / [arr := ...]) replaces the store with its VALUE
   (never a Store node as a value — the void-store badref chain), and the
   stored DATA is mapped too (the increment's inner load reads the SAME
   cell it writes — an unmapped read froze the counter at its init value,
   the array_local infinite loop).
2. **DEGRADATION REMOVED** (the user: "You should remove the degradation!
   It is just completely wrong!"): the hardcoded `degraded_subs` name list
   (modify_copy/transform/sum_fields/traverse/build/consume_mixed) AND both
   `"main"` gates (`stack_to_locals`'s + `region_split_plan`'s in
   bil2llvm.ml) are DELETED — no per-name refusals-to-convert anywhere.
   Un-masking it exposed (and this session FIXED) three real conversion
   bugs the name-gates had been hiding:
   - **the outgoing-arg lane** (`has_outgoing_stack_args`): a call-tail
     RSP-relative stack store with tag lo<0 and k>=0 (the pushed 7th-arg
     cell, [mem[RSP] := 1] of inc(...,1)) is callee-visible ABI traffic —
     the callee reads it at [hike_stack + |k|]; the sub with such traffic
     cannot be region-split (the factorial SIGSEGV class). The RETURN
     EPILOGUE ([call #t with noreturn] — the DCE target) is NOT a call
     block for this rule ([is_real_call]: Direct, or Indirect WITH a
     return — the prologue push inside an epilogue-terminated block must
     not land in any tail).
   - **the sp-escape rule** (`sp_escaped`): a stack-frame ADDRESS
     ([RBP - 0x30] — &cur) that ESCAPES (an arg-register def in a call
     block carrying a sp/fp-DERIVED value, or a derived value stored as a
     memory store's DATA at a non-bare-sp address) makes the frame
     addressable from outside — the sub cannot be region-split (the
     rec_struct SIGSEGV class: the callee walks p->next through the
     escaped pointer). The `derived` closure propagates through
     ARITHMETIC only (a Load's result is NOT derived — [mem[RBP-8]+1] as
     stored data has no sp-derived vars; the load's ADDRESS is not part
     of the VALUE — see [value_free_vars], the visitor-based free-vars
     minus memory-node internals). CONSERVATIVE (var-based, not
     def-site-based: a register that EVER holds a derived value counts);
     over-blocking costs precision, never correctness.
   - **the direct-const member rule**: a region member whose own access
     address is NOT [sp/fp ± const] (the indexed [RBP + i*4 - 0x70] /
     dynamic [mem[RAX]] shapes) reads/writes the MODEL FRAME at emission —
     the write-closed rule blocks its region (the storage would split
     between the private alloca and the frame).
3. **EMITTER CAST PRESERVATION (`src/bil2llvm.ml`,
   `create_static_mem_access`)**: the same Map idiom at the emission side —
   the singleton-tagged big-frame access rewrites ONLY the matched memory
   node to a marker var bound to the built GEP access; the enclosing
   [pad:64[...]] cast survives to [create_cast] (the zext sits right at
   the load — the lost-old-emission shape; the raw i32 reaching an i64 phi
   slot was the array_local/union_overlap/va_arg_vacopy/variadic llc
   class). Visitor-based node finder + mapper (no AST pattern matching).

`dune runtest` is **0-FAIL** (`ALL CBAT TESTS PASSED` — the F1 lifetime
landmark F1-NEQ acceptance test now passes end-to-end, no relaxed assertions).

| Gate | Command | Current result |
|---|---|---|
| unit suite | `dune runtest` | **0 FAIL** (`ALL CBAT TESTS PASSED`) ✅ |
| corpus emission | `bash scripts/run_corpus.sh /tmp/corpus /tmp/heritage_f1f` | **32/32 rc=0** (this session's Finding-1 emission; surviving `hike: guarded:` warnings = the Unbounded class, benign) |
| structural asserts | `bash scripts/check_allocas.sh /tmp/heritage_f1f` | **128 passed, 0 failed** ✅ |
| semantics (all) | `bash scripts/semantic/run_semantic_all.sh /tmp/corpus /tmp/heritage_f1f /tmp/sem_f1f` | **29 PASS, 3 FAIL, 0 SKIP** of 32 emitted ✅ (the 3 = the SAME knowns below; every recovered sub — factorial/ptr_chain/sret_big/struct_by_value/rec_struct/array_local/deep_recursion — still PASS) |
| semantics (8-bin) | `bash scripts/semantic/run_semantic.sh /tmp/corpus /tmp/heritage_f1f /tmp/sem_f1f8` | **8/8 PASS** ✅ |
| probes | corpus_watch / precision_probe spot-checks (factorial, rec_struct, array_local, variadic, alloca_vla) | **PASS, 0 crashes** ✅ |
| property F1-NEQ | `dune runtest` (test_cbat) | **head max = K=0x64 exactly** (the Finite-fires-end-to-end acceptance test, STRICT) ✅ |
| precise (stack_r) defines | per-emission count | **6 defines** (unchanged — landmark changes do not re-tag) |
| FP micro-suite | fm2/fm4/fm6/fmc8 native-vs-lifted | NOT RE-RUN this session |
| coreutils PIE (103) | `coreutils_pipeline.sh` lift+test | NOT RE-RUN this session |

The 3 remaining semantic failures are the SAME pre-existing knowns (the
redesign tickets in `.scratch/one-frame-anchor-removal/`):
- **out_nested_struct** — per-region alloca split breaks the contiguous
  struct layout in memory. (T05: drop the anchor)
- **out_va_arg_vacopy** — caller/callee argument-area initialization on
  positive entry offsets. (T03: per-call alloca for va_list)
- **out_variadic** — same as va_arg_vacopy plus variadic argument
  indexing, AND the value-typed-address class. (T02: VSA audit + fix; T03)

Reference emissions: `/tmp/heritage_lmC` (THIS session ②'s green emission,
29/3, the current baseline), `/tmp/heritage_mapD` (commit ①'s emission),
`/tmp/heritage_lm11` (session 2's pre-fix emission, array_local llc failure),
`/tmp/corpus` (rebuilt 2026-08-29 after the /tmp wipe — all earlier reference
emissions are GONE).

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

- `src/progs/` artifacts: `*.ll` is gitignored except `baselines/**` (the
  Makefile that once cleaned progs/ is deleted — dune owns the build).

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
dune exec zz_scratch_probe/audit02.exe        -- "$B"          # legacy harness entry (default profile)
dune exec zz_scratch_probe/dump_tags.exe      -- "$B" main
dune exec zz_scratch_probe/dump_bil.exe       -- "$B" main     # [REMOVED — dup of dump_tags]
# vsa-debug profile only:
dune exec --profile vsa-debug zz_scratch_probe/wbig_diag.exe -- "$B"
dune exec zz_scratch_probe/stage_timer.exe    -- "$B"          # per-stage wall-time breakdown
dune exec zz_scratch_probe/conv_diag.exe      -- "$B"          # fixpoint non-convergence
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
  `sp` explicitly (`Hike.Abi.sp (Project.target proj)` / a fixture's `v64 "RSP"`).
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
