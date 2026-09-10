# AGENTS.md — hike

BAP (OCaml/dune) plugin that lifts x86-64 ELF binaries to LLVM IR (the `hike-convlir`
pass), backed by a vendored port of CBAT's value-set analysis (`src/cbat_vsa/`).
There is no README; `docs/*.md` and `docs/adr/*.md` are the design record.
**DOC BUG (recorded 2026-08-31):** `docs/hike-full-plan.md` — the "single
source of truth" for the stack-model endgame and the O-series performance
plan — is GONE and was NEVER COMMITTED (no git history; the O-series proposals
are unrecoverable from the repo). The surviving plan record is
`docs/trace-partitioning-plan.md`, `docs/adr/`, and the two live lane dirs
under `.scratch/`. The O-series was partially succeeded by the coreutils
differential gate in `.scratch/restriction-removal/spec.md` §5.

## Design principles (NON-NEGOTIABLE)

1. **CONCISE, SIMPLE, COMPLETE, ROBUST.**  The analysis must work completely on MOST
   binaries — arbitrary lifted x86-64, not just the corpus — and every change must
   keep the full chain green: `dune runtest`, the precision probe over `/tmp/corpus`,
   the corpus run (rc=0; only known diagnostics survive), `check_allocas.sh`, and the
   semantic harness.
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
   `constrain_cell_on_trace` (see `docs/trace-partitioning-plan.md`
   §9 for the full map).
5. **Soundness over precision, always.**  A sound over-approximation that loses
   precision is acceptable; an unsound narrowing (excluding a reachable value) is a
   bug — it is the array_local-class semantic failure.  The semantic harness is
   the oracle.
6. **Debug instrumentation is NOT COMPILED INTO the production binary.**
   The line is: any RUNTIME-VARIABLE behavior is debug; production emits FIXED
   diagnostics only, through ONE sanctioned channel:
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
     sha16) NEXT TO the installed plugin — the battery verifies it before
     running gates; an mtime-based check cannot catch a plugin built from a
     DIFFERENT tree (measured: identical sources, stale artifacts, mtime
     warning silent, corpus rc=0 — only the -O0/-O2 semantic agreement
     caught it).

   The debug executables (build in every profile; `enabled_if` vsa-debug for
   vsa_debug/wbig_diag; NEVER installed, NEVER on a production path):
   - `zz_scratch_probe/audit02.exe` (legacy harness entry, default profile),
   - `zz_scratch_probe/clpequiv.exe` (the differential referee: 2.86M-check
     sweep, wired into `dune runtest` as a `(test)` stanza),
   - `zz_scratch_probe/vsa_debug.exe` (fixture traces, views, live maps),
   - `zz_scratch_probe/wbig_diag.exe` (w_big address inspection),
   - `zz_scratch_probe/stage_timer.exe` (per-stage pipeline wall-time
     breakdown — the profiling driver),
   - `zz_scratch_probe/conv_diag.exe` (fixpoint NON-CONVERGENCE diagnosis:
     prints the first still-growing (block, successor), the widening-point
     set, the failing blocks' BIR, and the gap successor's words/memory),
   - `zz_scratch_probe/dump_tags.exe` (vsa_info tag + split_plan dump),
   - `zz_scratch_probe/region_diag.exe` (per-sub pointer-arg denotations +
     the region plan — the region/materialization diagnostic; the former
     escape_diag, renamed when the escape died),
   - `zz_scratch_probe/dead_diag.exe` (the Dead-classification chain:
     which def classified Dead and why — the `hike: guarded: ... classified
     Dead` diagnostic's instrument),
   - `zz_scratch_probe/subtimes.exe` (per-sub producer cost distribution —
     the A/B workhorse), `passcost.exe` (per-sub pass + DCE-round times),
     `idstab.exe` / `sweepcheck.exe` (cross-process / in-process
     region-id determinism), `edgemulti_probe` (owner-pinned
     duplicate-pred-phi repro).
   NEVER add temporary debug prints / env-gated
   `Sys.getenv` instrumentation to production `src/` or `src/cbat_vsa/` code —
   keep the production sources clean; use or extend the debug harness instead.
   Build/run:

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
8. **STRICT CONTEXT.md ADHERENCE & NO AD-HOC BIL PATTERN MATCHING.**
   - **No AST Pattern Matching for Memory or Registers**: Never write structural `match` patterns over BIL constructors (`Bil.Load`, `Bil.Store`, `Bil.Cast`, etc.) or inspect memory operands directly. Use `Exp.visitor` or `Term.visitor` exclusively.
   - **Target-Defined Stack Pointer (`Abi.sp`)**: Never hardcode register strings like `"RSP"` or `"RBP"` or check for frame pointers. `Abi.sp` is the sole origin for stack derivation. **SP-only (ADR 0008): RBP/fp is an ordinary callee-saved GPR — the `Abi.fp` field, `is_fp`, `is_stack_reg` are DELETED; a register's stack-ness is PROVEN by the value-based VSA tag, never assumed by name.** (`Targetutils` and `Calling_conventions` are DELETED — the standalone `Hike_abi` library (unwrapped, module `Abi` inside each consumer via a one-line alias; exported as `Hike.Abi`) is the ONLY home of register lists, register predicates, and convention facts, shared by the vendored VSA libraries and production. NOTE: the module must never be named `Abi` at the LIBRARY level — BAP ships its own core `abi` plugin (module `Abi`, dynlinked into every bap process), and a bundle-internal `Abi` fails at load with "interface mismatch on Abi"; hence the library/module `hike_abi`/`Hike_abi`.)
   - **100% VSA Tagging Invariant**: Every definition with a `stack_access` tag MUST receive a `vsa_info` tag (`Range`, `Infinite`, `Unbounded`, `Dead`, or `VLA`). Untagged stack accesses are strictly prohibited.
   - **Lattice and Abstract Domain Values**: Dataflow propagation must operate over abstract sets and lattice values, distinguishing pointer arithmetic from memory values without AST inspecting hacks.


## Build & test

- Root is a dune workspace (`src/`, `test_cbat/`, `zz_scratch_probe/`): `dune build`,
  `dune runtest` (plain-OCaml check suite, no oUnit; prints `ALL CBAT TESTS PASSED`;
  includes the clpequiv differential referee as a `(test)` stanza).
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
2. `hike-vsa` — fills `Convutils.vsa_info` (sub tid → per-def SP-relative offset ranges
   per-def offset ranges — the possible range of each access, nothing
   else) by COMPOSING the ONE producer chain (arch review #1, ADR 0005;
   ADR 0003 LANDED — the `hike-relevance` pass, the `relevant` tag, and the
   backward-lane refineable gates are DELETED, every def is denoted, and
   `vsa_info` is the only carrier of stack-access-ness):
   `fixpoint → Cbat_vsa.Cbat_extraction.extract` (the M6 classification walk, the kind
   enum — `Convutils.vsa_kind`'s physical home — the k-range arithmetic, the
   set-overlap merge, the VLA matcher) `→ Hike_stack_model.{frame_escapes, regions_of_sub,
   split_plan}` (the pure stack model, split from the rewrite pass).  The record is built
   complete at one site; `hike_vsa` keeps only the pass policy (the
   degraded/non-converged arms).  No prefilters, no re-entrancy skip — every
   sub runs the full chain unconditionally (the no-gates lane, 2026-09-09)
3. `hike-stack-to-locals` — ONE registration, two rewrites (mem-fission's two
   halves: the DCE load-roots rule is defined over the vars the rewrite
   creates; neither runs without the other):
   (a) VSA CALCULATES, stack-to-locals only MERGES: collects the
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
   (b) `hike-dce` (the module; `Hike.Dce`) — the aggressive DCE lane: replaces the
   lifted RETURN epilogue (`#t := mem[RSP]; RSP := RSP + 8; call #t with noreturn`)
   with the var-free target so the popped-address def dies, then sweeps never-used
   defs to a fixpoint (the emitter emits a real LLVM `ret` regardless)
4. `hike-convlir` — emits LLVM via `bil2llvm.ml` through the ONE seam
   `Bil2llvm.emit_program` (sig-collection + declarations + bodies all
   inside; the KB context vars are internal — see `src/bil2llvm.mli` and
   CONTEXT.md's Emission Entry)

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
- The restriction is **GONE** (ADR 0003 landed; the no-gates lane finished it
  2026-09-09): `docs/adr/0003-remove-restriction-vsa-seeding.md` +
  `.scratch/restriction-removal/spec.md` deleted the `relevant` tag, the
  `hike-relevance` pass, and the backward-lane refineable gates; `vsa_info`
  (the VSA's two-channel frame-residency proof) is the only carrier of
  stack-access-ness, `denote_def` denotes EVERY def unconditionally, and VLA
  detection (`detect_dynamic_alloc`) lives in `cbat_vsa`, called once per sub
  from `hike_vsa`.
- Backward refinement (the trace-partitioning design —
  `docs/trace-partitioning-plan.md`, ADR 0002): GATE-FREE, SINGLE-PASS.  The
  deep backward walk (`refine_edge`: the producer subtraction
  (`cstr' = cstr ∩ post(v)`) confining each pre-image to its own def's produced
  values, the trace-exact cell meets (`constrain_cell_on_trace`)) runs INLINE
  at every conditional jump inside the forward fixpoint.  Every operand/def/shape
  has a complete rule (`operand_constraints`, `def_constraints`); a rule's
  identity (top / no constraint) is the sound answer, never a gate or a bottom.
- Keep the `set_stack_0` anchor tag; the fixpoint is a **Bourdoncle WTO fixpoint**:
  WTO ordering stabilizes inner SCCs before outer, widening only at WTO heads after
  10 warmup sweeps (landmark-directed: `Finite` extrapolates, `Zero` advances and
  joins, `Inf` standard-widens), always runs, no fallback. `not_implemented` always
  degrades to top with a logged warning.
- Widening is LANDMARK-DIRECTED — the FAITHFUL port of Simon & King, "Widening
  Polyhedra with Landmarks" (APLAS 2006; the paper PDF is tracked at the repo root):
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
  doubt (a non-singleton RSP or an unbounded arg).  The L-E1 +8 matched-
  pair restore is CONDITIONAL on the call block writing RSP (L-E1b: the FP-intrinsic
  calls — BIR Calls with no stack push — drifted RSP by +8 per intrinsic call;
  measured +0x48/iteration in mixed_fp_int's FP loop → the widen walked it to an
  infinite step-8 CLP).  Together these closed the -O0 corpus w_big (window ≥ 2^63)
  class to 1 (alloca_vla's VLA div — the runtime-arm class); the -O2 corpus
  (same sources at -O2) measures 95.05% ldstk exact with 4 w_big (the NEQ-guard
  class — `jne` counters can't be refined; the two-sided constraint is not
  CLP-representable).
- The emitter's untagged stack access is a WARNED POISON (bil2llvm.ml
  "hike: guarded: ... dead-path poison") instead of a `failwith`: the va_arg
  alignment-split dead branch's u128 stores (the concretely-dead misaligned path)
  previously crashed the whole pass; the poison is never executed (the block is
  unreachable).
- Drivers: `dune exec test_cbat/corpus_watch.exe -- <bin>`, `dune exec test_cbat/precision_probe.exe -- <bin>`.
- Env toggles: NONE in production (since 2026-09-03 — `HIKE_VSA_DEBUG`
  is deleted, and the build blocker bans every env read in src/; debug
  output is compiled in only under `--profile vsa-debug`). Test/probe
  code only: `HIKE_VSA_DIAG_BOTTOM=1` (precision_probe).

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
  `%frame` alloca per memory-touching define (1:1; stack-free defines exempt).
- `semantic/run_semantic.sh` → llc + `harness.c`, byte-diff stdout vs native, against EVERY
  emitted corpus binary (`out_*.ll`); setjmp modules link `setjmp_stub.S`.
  The LIFTED-executable link stays `-no-pie` — a constraint of the harness artifact
  (baked @got.plt constants + extern_weak .rodata refs would force a rejected
  DT_TEXTREL under `-pie`), NOT a corpus fallback; see run_semantic.sh's header.
  (Promoted from legacy 8-bin harness to full corpus suite 2026-09-07).
  PINNED-KNOWNS MODE (2026-09-09): a 4th argument (a golden-list file —
  `semantic/o2_known_failures.txt` is the -O2 corpus's) flips the gate green
  rc=0 iff the failing set equals the golden list EXACTLY; any difference is
  red rc=1 — newly failing = REGRESSION, golden-listed now passing =
  IMPROVEMENT — so a red-list change is a deliberate golden-list + record
  update, never a rider. Without the 4th arg: strict mode, rc=1 on ANY failure.
- `semantic/run_semantic_opt.sh` → the OPTIMIZATION-SAFETY gate (2026-09-01): the
  same native-vs-lifted equivalence but with `opt-21 -O2` inserted between rename
  and llc — what a real consumer's optimizer does to the module must not change the
  lifted binary's behavior.  STRICT (exit 1, no allowlist, no exemptions); on
  failure it AUTO-BISECTS every single pass (`mem2reg sroa instcombine …`) and
  prints the full broken-by list (a `CRASH` marker = opt crashed on that pass,
  the fixpoint class).  Keeps `<name>_renamed.ll`/`<name>_opt.ll` as reproducible
  artifacts.  The pinned optimizer is `opt-21` (system LLVM 21; the emitter binding
  is 19.1.7 — the gate deliberately tests the modern consumer; NO FALLBACK if
  opt-21 is missing).  The red list is the work-list
  for the optimizability program.

## Test honesty

The unit suite's `check` (test_cbat/test_common.ml) is a plain
assert-and-count: a check either passes, fails, or is deleted. There is
NO xfail, no stub, no substring-mute, and no other mechanism by which a
check can print success without asserting. (A 22-entry
`ignored_substrings` list used to short-circuit the harness: 38 sites
printed `ok: … (stubbed)` while asserting nothing — of which 22 were
measured to PASS and 16 to fail. It is deleted — the honest-gate lane,
2026-09-07.) A check that cannot be asserted is deleted, and its
home — if any — is the corpus battery.

`test_fixtures.ml` is the suite's shared fixture vocabulary (the `mk_*`
builders, consolidated by the fixture-lib lane — pure relocation).  A
builder with no caller is deleted like any dead code.  Builders produce
BIR subs/blocks/defs and `vsa_info` values only; tests call `Kb.provide`
explicitly at their own sites (the global KB write stays visible where
it happens).

## CURRENT VALIDATION STATE — refresh after EVERY change

Historical lane records and specs cited below live in git history (the
2026-09-09 records purge archived merged lanes' `.scratch/` dirs);
`git log --diff-filter=D --name-only -- .scratch/` finds them.

**Last verified: 2026-09-10 EEST — T4b LANDED (branch
`tm/t4b-conversion-correctness`): the conversion-correctness classes are
constructed away — THE -O0 PRIMARY ORACLE IS GREEN AT 37/37, strict
opt-safety 37/37, the -O2 pin SHRANK 9 -> 7 (fn_escape, fn_table_disp
flipped green)**

T4's merge battery (32/5 -O0, inventoried reds) is superseded by this
lane. Ticket `.scratch/typed-model/tickets/T4b-conversion-correctness.md`
+ verdict `T4b-conversion-correctness-verdict.md`; battery
`/home/tovpr/tm-battery/t4b/` (emissions `emit-o0`/`emit-o2` are the NEW
reference emissions; reference for -O0 byte-identity was merge-t4's).

The FOUR constructed rules (one mechanism each, at the point the wrong
value was produced; the evidence and case-count delta are in the
verdict):
1. **extraction (cbat_vsa.ml)**: a memory def whose address denotation
   is TOP is tagged `Unbounded` — the classification is total over the
   denotation trichotomy (stack-symbolic / provably-foreign / unknown).
   The unknown class previously fell silently into the foreign lane, so
   the partition could not see it; tagged, `accesses_served` reads it
   and the storage lattice joins the sub to Frame — ONE storage for
   every cell the raw lane and the converted cells touch (the
   struct-copy class: build's ranged array store was TOP-addressed and
   untagged while the copy-out's singleton reads converted to slot
   locals — split storage, the checksum read zeros).
2. **emitter, Caller lane (bil2llvm_mem.ml)**: the def's mem node is
   served by its FACT — promoted slot param (width-coerced), retaddr
   undef, or the window materialization — by VALUE SUBSTITUTION into
   the rhs (`rewrite_mem_node`, shared with the pointer lane). The
   whole-def replacement arms are DELETED (they dropped the def's
   surrounding rhs: e_two's `eax ^ [rbp+0x10]` lost the xor and b).
3. **emitter, outgoing slots (bil2llvm.ml/bil2llvm_mem.ml/
   bil2llvm_calls.ml)**: the site's slot value is recorded by the
   STORE's own emission (`fr.store_vals`, keyed by the storing def);
   the call passes the value the store WROTE — the late evaluation of
   the stored exp at the call is DELETED (a var the block redefines
   between the store and the call passed the wrong value: transform's
   slot0 got cell2's value because RAX was redefined). The Store lanes
   now return the stored data — Bil.Store's exp VALUE is the data, not
   the void store instruction.
4. **producer, callee_side (hike_vsa.ml)**: a store into the caller
   window demotes every slot cell its bytes intersect — SUB-SLOT writes
   too (a write at entry_rsp+68 is inside slot 7's cell) — and the
   written slots leave the promoted map: their reads take the window,
   where the write landed, never the stale parameter (modify_copy's
   `s.a0 += 100` store-back was read back as the original param).

| gate | result |
|---|---|
| build, default + vsa-debug profiles | rc=0 ✅ |
| instrumentation blocker | clean (rc=0) ✅ |
| referee (`clpequiv`) | **2,861,148 checks / 0 mismatches** ✅ |
| `dune runtest` | 516 ok; failure set == EXACTLY the 8 pre-existing (E2eD-7/8, LM F1-*); the F1-2 pin re-derived (it froze the old unsound not-seeded behavior of the TOP class) ✅ |
| -O0 emission / structural asserts | 37/37 rc=0 / 185 passed 0 failed ✅ |
| **-O0 strict semantics** | **37 PASS / 0 FAIL — the primary oracle green** ✅ |
| -O0 strict opt-safety | **37 PASS / 0 FAIL** (array_local's opt failure resolved) ✅ |
| -O2 emission / structural asserts | 37/37 rc=0 / 185 passed 0 failed ✅ |
| -O2 pinned semantics | **30 PASS / 7 FAIL — PIN SHRANK 9 -> 7**: fn_escape, fn_table_disp flip GREEN (proven); the golden list + comments updated in this lane's commit ✅ |
| convergence vs merge-t4/conv.log | array_local, fn_escape, fn_table_disp, nested_struct, sret_big, struct_by_value moved to SAME/SAME; no regressions; the seven DIFF rows == the pin's seven ✅ |
| provenance | bundle `06b009e387d37dc3` (final tree) ✅ |

The pin's remaining seven, re-attributed with current symptoms:
byte_copy/union_overlap (L3 SSE, value divergence), va_arg_mixed (L1
poison arm, SIGILL), fizzbuzz_safe (L1 poison arm, SIGILL), va_arg_vacopy
(the va_list round-trip, T9), spill_many (SIGSEGV at the -O2 frame
layout under the promoted model — T4's regression persists, needs its
own dig), jump_table_sw (the -O2 indirect-jump dispatch, rc=192).
Re-baseline: -O0 emissions 20/37 byte-identical to merge-t4's (17
changed: the Frame-joined subs + the promotion lanes); -O2 28/37. The
new Unbounded warnings (once per sub: pointer-arg derefs now WARN) are
the sanctioned diagnostic reaching the TOP class — the corpus rc gates
are unaffected.

**Last verified: 2026-09-10 EEST — T3c LANDED (the escape dies entirely; the
**Last verified: 2026-09-10 EEST — T3c LANDED (the escape dies entirely; the
denotation is the ONE mechanism; the -O2 pin 6 → 4) — the typed-model
program's waves 1–2 are complete, T4 is the frontier**

Merge `7a41070` + spec records `92ac41c`; ticket
`.scratch/typed-model/tickets/T3c-single-predicate-verdict.md`; battery
`/home/tovpr/tm-battery/t3c/` (pre-T3c baseline verified byte-identical
33/33 to merge-t3 before any change); plugin bundle `54e284d5d3441228`
(src `e7b3c1c9db41c52b`):

- The escape is DELETED ENTIRELY (`frame_escapes`/`frame_escaped`, the
  SP-derived closure `sp_derived_closure`, `sp_escaped`,
  `frame_addr_alias`, `def_facts`, `outgoing_arg_stores`,
  `sp_displacement`, `bounds_of` — grep-clean per the verdict's
  no-caller proofs). The region partition (`regions_of_sub ~sol`)
  decides from the tags + the denotations alone (stack-reachable =
  an address operand's denotation is a stack-symbolic set); ONE
  predicate family, no second channel.
- The pin moved 6 → 4 (fizzbuzz_safe, fptr_table flipped green — the
  L1-residual/L4 classes); golden list `o2_known_failures.txt` = the
  four (byte_copy, union_overlap, va_arg_mixed, va_arg_vacopy).
- Honest emission cost recorded: 19/33 -O0 binaries differ — 21 subs
  returned to the Frame model (unservable traffic under the
  caller-shared/`llvm.stacksave` SP anchor); the servability clause is
  written to be DELETED by T4's SP Slot. The entry sub's SP binds via
  `llvm.stacksave` as the T4 bridge.
- The program's remaining tickets: **T4** (stack-arg promotion + the SP
  convention + VSA-resolved indirect calls + thunks; worktree
  `/home/tovpr/hike-t4`, branch `tm/t4-stack-args`), then T5 (SSE
  lane) and T9 (va_list re-model), each blocked-by the previous wave.
  T4's retirement inventory (T3c's BLOCKED-BY-T4 section) lands in T4.

| gate (the merged battery) | result |
|---|---|
| -O0 emission / semantics / opt-safety | **33/33 rc=0 / 33 PASS 0 FAIL / 33 PASS 0 FAIL** ✅ |
| -O2 emission / semantics pinned | **33/33 rc=0 / 29 PASS 4 FAIL, set == golden (4)** ✅ |
| structural asserts (both lanes) | **165 / 0 each** ✅ |
| referee | **2,861,148 / 0 mismatches** ✅ |
| unit suite | failure set == the pre-existing 8 (E2eD-7/8, LM F1-*; owner triage) ✅ |
| plugin provenance | bundle sha16 `54e284d5d3441228` ✅ |

**Last verified: 2026-09-11 EEST — T4 + T4b LANDED (the promotion +
SP Slot + resolved indirect calls + internal thunks; strict -O0
restored to 37/37; the pin at 7)**

Branch `typed-model-program`, merges `9b06689` (T4) + `04b84c2` (T4b);
battery `/home/tovpr/tm-battery/merge-t4b` (plugin bundle
`06b009e387d37dc3`):

- **T4 (the grilled conversion)**: stack args promoted to real call
  parameters (per-slot, widest+trunc, written slots demote); the SP
  Slot (entry-block alloca, per-invocation anchor; `hike_stack` is
  zero in src/ and emissions); VSA-resolved indirect calls
  (singleton → direct promoted call; multi/foreign/TOP → pointer call
  through INTERNAL thunks whose signature matches the pointer-call
  layout; fn-pointer data renders to twins); the `hike_window`
  parameter (the variadic/mixed residual only); retaddr reads bind
  undef. All 21 T3c re-framed subs recovered their exact region
  counts. Convergence prize: many_args 58/4, mixed_fp_int 68/4,
  variadic 185/27.
- **T4b (conversion correctness)**: T4's guard diagnosis was
  superseded — the copy's values were lost to SPLIT STORAGE (an
  untagged TOP-addressed store made the partition zero-init the
  copy-out's reads) and STALE-SLOT READS (call sites re-evaluated
  stored exps). Four constructed rules, zero gates: Unknown seeding
  (TOP-addressed defs tag Unbounded), the Caller lane serves the node
  via value substitution, slot args consume the STORED value, written
  slots demote from promotion. Two unsound implicit case-fusions
  deleted (TOP⇒foreign; written-slot reads⇒parameter); net diff
  +176/−94. strict -O0 32/5 → **37/37**; fn_escape/fn_table_disp
  proven flips; six more sources converged SAME/SAME.
- **The -O2 pin holds at 7** (byte_copy, union_overlap — L3/T5;
  va_arg_mixed, fizzbuzz_safe — L1; va_arg_vacopy — T9; spill_many —
  the one undug T4-merge SIGSEGV, next lane's first dig;
  jump_table_sw — the -O2 indirect-jump dispatch).
- NOTE: the corpora are 37 bins (T4 rebuilt `/tmp/corpus*` in place,
  against its isolation instruction — the canaries verify the lanes;
  the state is recorded). The Unbounded diagnostic now fires once per
  Frame-joined sub's pointer-arg derefs (27 -O0 lines — the sanctioned
  channel).

| gate (the merged battery) | result |
|---|---|
| strict opt-safety (-O0) | **37 PASS / 0 FAIL** ✅ |
| -O0 emission / semantics / allocas | **37/37 rc=0 / 37 PASS 0 FAIL / 185-0** ✅ |
| -O2 emission / semantics pinned / allocas | **37/37 rc=0 / 30-7 set == golden / 185-0** ✅ |
| referee | **2,861,148 / 0 mismatches** ✅ |
| unit suite | failure set == the pre-existing 8; all T4 pins pass ✅ |
| plugin provenance | bundle sha16 `06b009e387d37dc3` ✅ |

Reference emissions: `/home/tovpr/tm-battery/merge-t4b/emit-{o0,o2}`.
Next: S10a (the dead-weight wave), S10b (the convutils split), T5,
T9, then the final code review.

**Last verified: 2026-09-10 EEST — T3c LANDED (the escape deleted
entirely; the partition reads the denotations; the -O2 pin moves 6→4)**

Branch `typed-model-program`, merge `7a41070` + specs `92ac41c`;
battery `/home/tovpr/tm-battery/merge-t3c` (plugin bundle
`54e284d5d3441228`):

- The escape QUESTION died (owner doctrine: the symbolic stack base
  answers everything): `frame_escapes`, `frame_escaped`,
  `sp_derived_closure`, `outgoing_arg_stores`, `def_facts` and their
  helper machinery are DELETED with no-caller proofs; `regions_of_sub`
  takes the solution and reads the denotations directly (one predicate
  family). The -O2 pin moved 6→4 (fizzbuzz_safe, fptr_table flip
  green; 12 convergence quality-rows improved) — the owner's
  "more precise and correct" prediction held. The golden list is at 4
  (byte_copy, union_overlap, va_arg_mixed, va_arg_vacopy).
- INVENTORY (conversion-first; NOT fixed): the `prove_nonneg`
  seed-flag's denotational replacement measured red (L-D2/L-D6) and
  was reverted — reproduction in the T3c verdict; 21 subs honestly
  returned to the Frame model (precise only via the closure's
  accident) pending T4's SP-Slot anchor; the entry sub's SP binds via
  `llvm.stacksave` as the bridge.
- The program spec was rewritten to the landed state: T4's grilled
  design (VSA-resolved indirect calls, internal thunks, the SP Slot,
  caller_window), T5 re-scoped, T9 (the va_list re-model) ticketed.

| gate (the merged battery) | result |
|---|---|
| strict opt-safety (-O0) | **33 PASS / 0 FAIL** ✅ |
| -O0 emission / semantics / allocas | **33/33 rc=0 / 33 PASS 0 FAIL / 165-0** ✅ |
| -O2 emission / semantics pinned / allocas | **33/33 rc=0 / 29-4 set == golden / 165-0** ✅ |
| referee | **2,861,148 / 0 mismatches** ✅ |
| unit suite | failure set == the pre-existing 8 (T8, owner triage) ✅ |
| plugin provenance | bundle sha16 `54e284d5d3441228` ✅ |

Reference emissions: `/home/tovpr/tm-battery/merge-t3c/emit-{o0,o2}`.
Next: T4 (the grilled promotion + SP convention), then T5, T9.

**Last verified: 2026-09-10 EEST — T3 LANDED (the symbolic stack base +
single-channel tagging; the offset fiction and `value_env` are GONE)**

Branch `typed-model-program`, merge `d2b66d7` + records `52b47c1`;
battery `/home/tovpr/tm-battery/merge-t3` (the same tree the finisher
verified as `7a60794`; plugin bundle `0311e8475e2aaf1e`):

- The word domain carries the bounded stack segment
  (`[2^62, 2^62+8MiB]`, `StackOff`): arithmetic propagates the symbol,
  bitwise/compares go TOP-unknown (the L1 class is structurally
  impossible; `value_env` deleted). `is_stack_access addr st` = the
  denotation is a stack-symbolic set; the tag = the denotation minus
  the base — ONE channel; the frame relation (`seed_frame`,
  `apply_frame_def`, `frame_add_fvar`, `mentions_frame_var`,
  `rewrite_addr`) is deleted grep-clean. The emitter materializes
  addresses through the ONE uniform rule (`ptr = frame +
  (word − stack_0)`); the Mixed class (two-sided spans — the va_list
  reg-save-or-overflow pointer) uses the argued two-base
  `select(word ≥ stack_0, hike_stack + (word − stack_0), raw word)` —
  a complete rule per span shape, never a refusal (spec §T3's landed
  note). Design notes: `.scratch/typed-model/t3-design-notes.md`;
  verdict: `tickets/T3-symbolic-stack-base-verdict.md`.
- The 7 old-universe pins re-derived and green (VSK-EMPTY, L-D6, L-D2,
  L3c5-3a/b, L3c4-4, L3c3-1). Deliberate full -O0 emission
  re-baseline (all 33 binaries: folded constant frame GEPs → runtime
  `word − %anchor_i64` arithmetic; 3 selects corpus-wide; inttoptr
  counts ~unchanged).
- **va_arg_vacopy re-attributed**: the recorded L2 mechanism (missing
  `rebase_addr` in the `lo<0` arm) is structurally deleted and the
  -O2 failure persists → the residual is the va_list state round-trip
  in the -O2 lift (golden comment corrected, commit `52b47c1`).
  va_arg_mixed stays L1 (the ud2 poison arm, rc=132). Convergence
  rows unchanged in classification (27 SAME/SAME + the six DIFF);
  quality-only movement: va_arg_vacopy's -O0 lift post-opt 212→396
  (T4's lever).

| gate (the merged battery) | result |
|---|---|
| strict opt-safety (-O0) | **33 PASS / 0 FAIL** ✅ |
| -O0 emission / semantics / allocas | **33/33 rc=0 / 33 PASS 0 FAIL / 165-0** ✅ |
| -O2 emission / semantics pinned / allocas | **33/33 rc=0 / 27-6 set == golden / 165-0 (modernized check (d))** ✅ |
| convergence | **27 SAME/SAME + the six DIFF = the knowns** ✅ |
| referee | **2,861,148 / 0 mismatches** ✅ |
| unit suite | failure set == the pre-existing 8; the 7 modernized pins PASS ✅ |
| plugin provenance | bundle sha16 `0311e8475e2aaf1e` ✅ |

Reference emissions: -O0 `/home/tovpr/tm-battery/merge-t3/emit-o0`
(T3 re-baselined all 33), -O2 `.../emit-o2`. Next: T4 (stack-arg
promotion), T5 (the SSE lane def-use).

**Last verified: 2026-09-10 EEST — THE TYPED-MODEL PROGRAM, WAVE 1
LANDED (T1 + T2 + T6 merged on `typed-model-program`) + THE -O2 CORPUS
INCIDENT FOUND AND REPAIRED (the pin holds at 27/6, set == the golden
six)**

The implement-spec PR branch `typed-model-program` (tickets + verdicts
in `.scratch/typed-model/`), battery `/home/tovpr/tm-battery/merge-t1`:

- **THE -O2 CORPUS INCIDENT (found by the owner challenging a
  too-good result)**: a sp_reload-era rebuild invoked
  `compile_corpus.sh /tmp/corpus_o2` — the underscore misses the
  script's `-o2`-suffix test, so the script built -O0 BINARIES into
  `/tmp/corpus_o2` (byte-identical 33/33 to `/tmp/corpus`) while the
  real -O2 lane went to `/tmp/corpus-o2`. Every -O2 measurement
  consuming the underscore dir silently re-tested -O0 binaries: one
  battery "passed -O2 strict 33/33" on them, the convergence table
  read SAME/SAME with i0=i2, and the golden list was briefly and
  WRONGLY emptied (commit 7cfa53a — superseded by the correction
  commit). The tell: deep_chain's -O2 lift is compiler-folded to ~4
  insns (a genuine -O2 build cannot un-fold); i0/i2=323/323 exposed the
  fake corpus. REPAIRED: `/tmp/corpus_o2` restored from
  `/tmp/corpus-o2`; the mislabeled copy kept at
  `/tmp/corpus_o2.MISLABELED-o0copy`; `scripts/battery.sh` now
  canary-guards the lanes (byte_copy/fizzbuzz_safe must DIFFER from
  -O0 or the battery hard-fails).
- **T1 (the opt-safety regression, P0)**: the typed frame GEP now
  REQUIRES the producer's frame-residency license (`frame_wrap_license`
  in `src/convutils.ml`; `create_def` derives it from the def's tag —
  `Range`/`Infinite` with `lo < 0` = this frame; `Unbounded`/`VLA`/
  untagged keep the inttoptr exception lane). The old wrap told LLVM
  EVERY runtime address integer was based on this sub's frame alloca,
  so opt-21 deleted the sret copy stores after inlining
  (struct_by_value, nested_struct). Mechanism + evidence:
  `.scratch/typed-model/tickets/T1-opt-safety-regression-verdict.md`
  (its -O2 rows are void — measured on the mislabeled corpus; the
  verdict carries a correction note). Emission re-baseline: 14/33 -O0
  binaries changed (runtime-index frame wraps 201→72, inttoptr
  42→171); the two failing binaries became byte-identical to the
  opt-green offset-model reference.
- **T2 (the simplification pass)**: −41 LOC — proven-orphaned values
  (`equal_int64_pair`, `Cbat_word.hash`, …), mli over-exposures,
  stale comments; behavior-identity structural. Verdict:
  `.scratch/typed-model/tickets/T2-simplification-pass-verdict.md`.
- **T6 (the data relocations, L4)**: section initializers render AFTER
  `emit_program`, through the same address map code references use
  (the function-start remap arm was structurally dead at initializer
  time — relocated fn-pointer addends rendered as raw input vaddrs).
  The rule fires for any binary relocating fn pointers into emitted
  data (the current -O2 fptr_table builds its table with `lea`s, so
  the real-corpus pin shows no movement from it). Verdict:
  `.scratch/typed-model/tickets/T6-data-relocation-rendering-verdict.md`.
- **THE PIN HOLDS AT 27/6 (verified on the REPAIRED corpus with the
  merged plugin)**: failing set == the golden six (byte_copy,
  fizzbuzz_safe, fptr_table, union_overlap, va_arg_mixed,
  va_arg_vacopy). No -O2 movement from wave 1 — as expected: T1's fix
  is the -O0 lane, T6's rule needs a fn-pointer-data binary the
  current corpus lacks. -O2 allocas 164/1 (out_struct, the recorded
  shape-d).
- **CONVERGENCE (real corpus)**: back to the recorded shape —
  deep_chain 323/4 etc. are the compiler's constant-folding of the -O2
  input (SAME, correct); the six DIFF rows are exactly the golden six
  (the L1–L4 classes T4/T5/T6 target). Table:
  `/home/tovpr/tm-battery/merge-t1/conv-real.log`.

| gate | result |
|---|---|
| strict opt-safety (-O0) | **33 PASS / 0 FAIL** (was 31/2) ✅ |
| -O0 emission / semantics / allocas | **33/33 rc=0 / 33 PASS 0 FAIL / 165-0** ✅ |
| -O2 emission / semantics pinned | **33/33 rc=0 / 27 PASS 6 FAIL, set == golden** ✅ |
| -O2 structural asserts | **164 passed / 1 failed (out_struct shape-d, the recorded class)** ✅ |
| convergence report (real corpus) | **27 SAME/SAME + the six DIFF = the knowns; deep_chain 323/4** ✅ |
| referee | **2,861,148 / 0 mismatches** ✅ |
| unit suite | failure set == the pre-existing 8 (E2eD-7/8, LM F1-*; T8, owner triage) ✅ |
| plugin provenance | bundle sha16 `29c2bb3d9e2e05a2` ✅ |

The -O0 reference emission for byte-identity checks is
`/home/tovpr/tm-battery/merge-t1/emit-o0` (T1 re-baselined 14/33);
the true -O2 emission is `.../emit-o2-real`. Next: T3 (the symbolic
stack base — the coordinated flip), then T4 (stack-arg promotion),
T5 (the SSE lane def-use).

**Last verified: 2026-09-10 EEST — THE CONVERGENCE INSTRUMENT (ticket 05)
+ THE TYPED MODEL'S OPT-SAFETY REGRESSION (2 binaries, triage next)**

`scripts/semantic/convergence_report.sh` runs the consumer's optimizer
(opt-21 -O2) on BOTH lifts (-O0 input and -O2 input) and classifies each
semantically (rc + stdout vs native), with instruction counts as the
quality dimension and the native -O2 text size as the
input-complexity reference. First baseline: for runtime-dependent
sources the two lifts already converge (sp_reload 82/82 insns,
bitfield_struct 5/5, setjmp_longjmp 45/45); the huge raw ratios
(deep_chain 323/4, ptr_chain 218/4) are the COMPILER's constant-folding
of the -O2 input — the -O2 lift post-opt is genuinely correct (SAME).

**REGRESSION FLAGGED BY THE INSTRUMENT, confirmed by the strict gate:**
the typed model breaks opt-safety for **nested_struct and
struct_by_value** (-O0: `run_semantic_opt.sh` = 31 PASS / 2 FAIL on
`/tmp/emit_typed_o0`; the recorded 32/32 was the offset model). The
built-in auto-bisect exonerates every SINGLE pass — the miscompile needs
a pass combination (ordering interaction), so the dig is non-trivial.
Until triaged, the typed flip is NOT shippable as green. Also
first-time-measured: the -O2 lifts post-opt diverge for rec_struct and
sret_big (pre-opt they pass) — same instrument, -O2 side.

| gate | result |
|---|---|
| strict opt-safety on the typed -O0 emission | **31 PASS / 2 FAIL** (nested_struct, struct_by_value) ⚠️ |
| convergence baseline | committed: `scripts/semantic/convergence_report.sh`; table in `/tmp/convergence_baseline.txt` ✅ |

**Triage status (2026-09-10, late):** the align-1 hypothesis (frame-routed
accesses claiming natural alignment) was TESTED and REJECTED — the
violations persist with byte alignment. The failing set is stable across
runs (not garbage-dependent). The single-pass auto-bisect exonerates
every pass; the miscompile needs a pass COMBINATION. Next diagnostic:
per-pair bisection (e.g. -O2 minus sroa/mem2reg/early-cse pairwise) and
the IR delta vs the offset-model emission (emit_l1_o0, which was
opt-green for both). The segment-seed WIP was REVERTED (commit series
9f52c93..c10f699): the seed alone broke the corpus 22/33 — the tags
became segment-absolute without the coordinated keying/tag
relativization; stage 1 of the symbolic-base program is the FULL
coordinated flip (seed + relativized tags + keys + the 7 pin
modernizations), not the seed alone. THE REFERENCE EMISSION REMAINS
`/tmp/emit_typed_o0` (pre-seed, re-emitted 2026-09-10 late, 33/33
semantics; provenance src=a1253ff6826d632e bundle=96dd7386358c5dbd).

**Last verified: 2026-09-10 EEST — THE SP-RELOAD CORPUSTEST (channel-2 pin):
the corpus is 33 binaries**

New `src/progs/synth/sp_reload.c`: a stack pointer is SAVED TO STACK
(volatile cell, the round-trip is real), reloaded, and dereferenced for
writes and reads at two frame depths — the VSA's channel-2 seeding (the
reloaded value is frame-resident and bounded) must tag the
reloaded-pointer derefs with concrete ranges. MEASURED: -O0 tags all
such derefs Range(...) and they convert to regions (zero inttoptr);
-O0 semantics **33 PASS / 0 FAIL**; allocas **165/0**; -O2 pinned green
at **27 PASS / 6 FAIL of 33** (sp_reload PASSES at -O2 too — the failing
set is unchanged). Both corpus lanes rebuilt (`/tmp/corpus`,
`/tmp/corpus_o2`, plus `/tmp/corpus-o2` from the same run); the typed
reference emissions gained `out_sp_reload.ll`.

**Last verified: 2026-09-10 EEST — THE TYPED FRAME GENERALIZED (ticket 04):
the offset access path is DELETED — the typed frame is THE model**

The `--hike-stack-model` parameter is gone (it existed for one session);
`create_inttoptr` was renamed **`create_addr_ptr`** — it materializes the
pointer for an address integer: frame-relative integers become GEPs into
the frame; real (non-frame) addresses — section/global constants,
foreign pointers — become inttoptr (the documented exception lane, ADR
0009). The VSA's residency tags license the conversion (the 100% Tagging
Invariant); untagged addresses are foreign pointers.

| gate (the final tree) | result |
|---|---|
| -O0: emission / semantics / allocas | **32/32 rc=0 / 32 PASS 0 FAIL / 160-0** ✅ |
| -O2: emission / semantics pinned / allocas | **32/32 rc=0 / 26-6 pinned green / 159-1 (recorded shape-d)** ✅ |
| referee | **2,861,148 / 0** ✅ |
| suite | failure set == the pre-existing baseline (8; owner triage) ✅ |
| **Re-baseline** | **20/32 binaries changed** vs the L1 reference (itemized in ticket 04) — **the new -O0 reference emission is `/tmp/emit_typed_o0`** ✅ |
| inttoptr/ptrtoint corpus-wide | **447 → 259** (exception lane + regions plumbing remain) ✅ |
| plugin provenance | bundle sha16 `818458b8d83db655` ✅ |

**Last verified: 2026-09-09 EEST — THE TYPED FRAME PROTOTYPE (ticket 03,
ADR 0009, `--hike-stack-model=typed`): the endgame's typed form lands
behind a pass parameter**

`create_inttoptr` routes address integers through the frame base as GEPs
when the typed model is selected (inttoptr survives only for
section/global constants — the exception lane); the default model is
byte-identical to the L1 reference (verified on byte_copy). Acceptance on
factorial/byte_copy/fizzbuzz_safe: **3/3 semantics PASS** and the opt
report (`scripts/semantic/opt_report.sh`): byte_copy post-opt **196→170
insns, 21→6 inttoptr/ptrtoint** (the escape-class binary — the thesis
proven); factorial/fizzbuzz_safe are precise (regions) and identical
under both models. The pin holds 26/6. ADR 0009 records the contract;
generalization is the next deliberate re-baseline lane.

**Last verified: 2026-09-09 EEST — THE L1 LANE (branch
`sp-only-stack-semantics`, uncommitted): the Dead misclassification
repaired at the producer + k_ranges removed + the -O2 pin moves 25/7 →
26/6**

Root causes and fixes live in `.scratch/o2-attribution/tickets/02-l1-dead-classification.md`.
In brief: (1) `reachable_jumps` now evaluates guards in `value_env`
(frame-tracked vars read as the unknown stack addresses they are, never
as the fake offset words) — the -O2 stack-realignment guard stopped
pruning a live loop; (2) `Clp.logand`'s `None -> bottom` (unrepresentable
image) is `None -> top` — principle 3; (3) `create_def` enforces the
lhs var's declared width at birth (the lifter's `-O2` lane defs emitted
i128 values under 64-bit vars; the loop phi then failed llc) — no phi
coercion; (4) **k_ranges are GONE from `vsa_info`** (the owner's
ranges-only doctrine): the pushed-arg discriminator is computed once in
the extraction (`outgoing_arg_stores`) and consumed by the escape
analysis internally — dropping it outright broke va_arg_vacopy/variadic
at -O0 (the oracle fired; measured, then restored as an internal fact).
The Dead arm now WARNS (`hike: guarded: ... classified Dead`) — one new
-O0 diagnostic line (va_arg_mixed's genuinely-dead misaligned arm).

**The 8 pre-existing unit-suite failures (E2eD-7/8, LM F1-*) fail on the
PRISTINE tip too (measured via `git stash`) — they pre-date this lane and
are the owner's triage item; the referee and both semantic oracles are
green.**

| gate (this lane's final tree) | result |
|---|---|
| unit suite | failure set == the pristine-tip baseline (8, pre-existing); POISON pin flipped to expect the warn ✅ |
| referee | **2,861,148 / 0 mismatches** ✅ |
| both profiles build | default + vsa-debug **rc=0** ✅ |
| corpus emission (-O0) | **32/32 rc=0** ✅ |
| -O0 semantics | **32 PASS / 0 FAIL** ✅ |
| -O0 structural asserts | **160 passed, 0 failed** ✅ |
| -O0 byte-identity vs cand3 | **29/32** — 3 itemized deltas (va_arg_mixed, va_arg_vacopy, variadic; the value_env refinement change), each oracle-proven; **the new -O0 reference is `/tmp/emit_l1_o0`** ✅ |
| -O2 corpus emission | **32/32 rc=0**; allocas **159/1** (out_struct, the recorded shape-d) ✅ |
| -O2 semantics, pinned | **26 PASS / 6 FAIL (pinned green)** — **array_local flipped**; fizzbuzz_safe residual = L3 (lifted-ud2 reached via L3-wrong lane values) ✅ |
| unmapped FP intrinsics | **0** ✅ |
| plugin provenance | bundle sha16 `3263becd53827d07` ✅ |

Artifacts: `/tmp/emit_l1_{o0,o2}`, `/tmp/sem_l1_{o0,o2,o2c}`,
`/tmp/dead_diag_fixed2.txt`; probes `dead_diag.exe` / `width_diag.exe`
added (the Dead-chain and width-mismatch diagnostics).

**Last verified: 2026-09-09 EEST — THE -O2 GATE PIN lane (branch
`sp-only-stack-semantics`, uncommitted): the -O2-corpus semantic gate's
failing set mechanically pinned**

No src change: a scripts/docs lane. The -O2 semantic red list was
re-verified end-to-end fresh (not from battery artifacts): a fresh
`run_corpus.sh` emission of `/tmp/corpus_o2` is **byte-identical 32/32**
to the battery's `cand-o2` reference (installed bundle sha16
`d018a1ee694ed6de` = the recorded final), and the gate fails the exact
recorded seven — no regression, no drift (the 19:46 run the same evening
failed the identical set). NEW: `run_semantic.sh`'s 4th argument
(pinned-knowns mode) + `scripts/semantic/o2_known_failures.txt` (the
seven + provisional per-binary class priors — NO per-binary -O2
root-cause analysis exists in the record; the dig of git history found
only the pre-purge verdict's loose class label, and the archive contains
zero -O2-level per-binary text). All four pin paths exercised: green
(7 knowns, rc=0), REGRESSION, IMPROVEMENT (rc=1, labeled + named), strict
mode unchanged. Class attributions in the golden file are PRIORS from
-O0-era/escape-falsification/precision-lane records, pending a real -O2
per-binary attribution pass.

| gate (this lane's actual runs) | result |
|---|---|
| fresh -O2 emission vs `cand-o2` | **byte-identical 32/32** (rc=0) ✅ |
| -O2 semantics, pinned | **25/7 (pinned)** — set == golden, rc=0 ✅ |
| pin red paths | REGRESSION + IMPROVEMENT both rc=1, correctly labeled ✅ |
| -O0 semantics, strict | **32 PASS / 0 FAIL**, rc=0 ✅ |

Ticket 01 (the attribution pass) then landed: the seven failures are FOUR
mechanisms, each runtime-proven — L1 emitter poison arms live
(fizzbuzz_safe patch-proven end-to-end, va_arg_mixed, array_local
partial), L2 missing hike_stack rebase in `bil2llvm_mem.ml`'s `lo<0`
dynamic-load arm (va_arg_vacopy), L3 SSE lane-promotion def-use
(union_overlap, byte_copy, array_local), L4 raw un-relocated data-section
addends (fptr_table). Several recorded priors KILLED (escape-class for
byte_copy, indirect-call for fptr_table, -O0-loop-bound for
fizzbuzz_safe, value-side-TOP for union_overlap). Ranked fix lanes L2 →
L1 → L3 → L4 with sizes in `.scratch/o2-attribution/verdict.md`; golden
comments corrected to the verdict (set untouched, pin re-verified green).

Artifacts: `/tmp/emit_fresh_o2`, `/tmp/sem_pin_{a,b,c,d}`,
`/tmp/sem_strict_o0`, `/tmp/sem_diag_o2` (the fresh-evidence run).

**Last verified: 2026-09-09 EEST — THE SIMPLIFICATION PROGRAM (branch
`sp-only-stack-semantics`, 4 commits `65b879c`..`3268217`): records purge +
trust-the-producer + the vendored VSA's no-gates conversions + the
architecture deepening — FULL BATTERY GREEN, repo 62.8k → ~40k lines**

The four lanes (from the 2026-09-09 architecture review, all four candidates
executed): (1) records purge — 34 archived `.scratch/` lanes, the AGENTS.md
history sweep (19 superseded entries), the duplicate paper text; the
surviving record is this section + the two live lane dirs + 3 perf reports.
(2) trust-the-producer — ONE KB accessor (`Hike_kb.info_of_sub`) replaces
seven private defaults; `split_plan` trusts the record; `frame_escapes`
narrows to the tag maps it reads (the producer's dummy record dies); the
model owns `frame_dims` (the emitter's duplicated tag folds and
`degraded_dims`' dead tuple halves die); `emit_program` populates its ctx's
abi/sp; STL carries the slot width in the cell shape. Dead code: interval
tree to its 8-function surface, map-lattice `Make`/`Make_indexed`/
`Free_index`, `vla_size_of_rhs`, `Clp.dir_of`, `Word.lsb`, `cbat_memo`
de-functorized, mli over-exposures unexported, 9 closed-lane probes + 7
stanzas + `profile_lift.sh` + 2 orphaned fixtures. (3) the vendored VSA's
no-gates conversions: div-by-{0} → the word semantics `{ones}` (D3-3/4 pins
rewritten), TOP-addressed stores → whole-memory top,
`constrain_cell` keys by the DENOTED rewritten address (the SP pre-check
and constant-only requirement gone), `segment_wordset` degrades to top,
`st_tag_of` adopts the exact tag value on top locals,
`complement_guard_op` EQ↔NEQ, NEQ joins the understood flag ops,
Infeasible seeds stay identity; the chain lane's single-def scope is
DOCUMENTED as the whole-sub map's soundness boundary (the deep walk is the
positional mechanism) — not a refusal to re-litigate: the audit's proposed
"meet into every producer" conversion is UNSOUND for the sequential-defs
class. (4) architecture — `Cbat_vsa.Test_seam` quarantines the fixtures'
surface out of the production interface (CONTEXT.md's Test Seam term); the
rewrite registrations merge (`hike-stack-to-locals` runs stl + dce — the
load-roots rule is defined over the rewrite's own vars); the orphaned
walk-record census deleted. NOT done, recorded: `create_branches`' >2-branch
failwith is an internal shape assert on a filter-guaranteed invariant (a
total cascade adds new-basic-block machinery to an unreachable lane — do
not re-propose); `Clp.compare` is interface-forced (it shadows the derived
one for Value.S); the wordset_intf shrink yields nothing (every member is
test-used through FinSet/Clp); the convutils split (review candidate 8) and
the `simplify_jmps` removal are future lanes (the latter renumbers TIDs
corpus-wide — a deliberate re-baseline, never a rider).

| gate | result |
|---|---|
| unit suite | `dune runtest` ALL PASSED, clpequiv **2,861,148 / 0 mismatches** ✅ |
| both profiles build | default + vsa-debug **rc=0** ✅ |
| corpus emission (-O0) | **32/32 rc=0**, diagnostics identical to control ✅ |
| IR vs same-tree control | lane 2: **byte-identical 32/32**; lane 4: byte-identical 32/32; lane 3: **1/32 delta** — alloca_vla's fallback frame 96→80 bytes (the div-fix/tag-adoption precision gain) ✅ |
| structural asserts (-O0) | check_allocas **160 passed, 0 failed** ✅ |
| semantics (-O0) | **32 PASS / 0 FAIL** ✅ |
| optimization-safety (opt -O2) | **32 PASS / 0 FAIL** ✅ |
| -O2 corpus | emission **32/32 rc=0**; allocas **159/1** (out_struct, the recorded shape-d class); semantics **25/7** — the recorded class is 24/8 (deep_recursion, fizzbuzz_safe, fptr_table, union_overlap, va_arg_mixed, va_arg_vacopy, array_local, byte_copy); **deep_recursion flipped GREEN** (lane 3's NEQ/cell-meet conversions) — strictly no-worse ✅ |
| unmapped FP intrinsics | **0** (both corpora) ✅ |
| probes | precision_probe + corpus_watch (alloca_vla) — **PASS, 0 crashes** ✅ |
| instrumentation blocker | clean (exercised by both builds) ✅ |
| plugin provenance | bundle sha16 `d018a1ee694ed6de` (final), recorded after every lane install ✅ |

Artifacts: `/home/tovpr/simplify-battery/{ctrl,cand,cand2,cand3,cand-o2,sem*,semopt*}`
(ctrl = pre-program control; cand2 = post-lane-3; cand3 = final).
The reference emission for future byte-identity checks is `cand3` (-O0) —
pre-lane-3 controls are stale for IR comparison only in alloca_vla.

**Last verified: 2026-09-09 EEST — NO-GATES LANE (branch
`sp-only-stack-semantics`, committed as `65b879c`) — the pipeline's last
guard-shaped conditionals DELETED — BATTERY GREEN, IR BYTE-IDENTICAL 32/32
to a same-tree control**

The lane (grilling-settled): a full-file:line audit of every conditional in
`src/` against the re-derived 4-test classification (provenance — domain
value vs distrust; re-derivation; soundness; fallback-to-identity) found 24
RULEs, 1 GUARD, 2 UNCLEAR. Deleted all three (the audit's full inventory is
in the session record; the audit also confirmed the absences: no
`hike-relevance` pass, no escape re-derivation in STL, no `addr_is_stack`
consult, no 100%-invariant WARN):
1. the vsa pass re-entrancy skip (`hike.ml` — `Map.is_empty` belt-and-
   suspenders, redundant with `~runonce:true` + the KB join domain),
2. `has_mem_ops` prefilter (`hike_vsa.ml` — mem-free subs now run the FULL
   chain unconditionally, so `degraded`/`frame_escaped` are the faithful
   values, never hardcoded false),
3. `clamp_hi` (`bil2llvm.ml` — the silent 0x40000000 cap that rewrote a
   producer tag's `hi` extent with no diagnostic; the tag is trusted).
STL confirmed compliant with the autonomy contract: the merge lives in the
producer; STL only maps tags to locals over the record's regions.

| gate (candidate vs SAME-TREE control on the current `/tmp/corpus`) | result |
|---|---|
| unit suite | `dune runtest` ALL PASSED, clpequiv **2,861,148 / 0 mismatches** ✅ |
| both profiles build | default + vsa-debug **rc=0** ✅ |
| corpus emission | **32/32 rc=0** (surviving diagnostics = the known guarded/undef classes) ✅ |
| **IR byte-identity vs same-tree control** | **IDENTICAL 32/32** (the earlier red3-o0/t06-o0 controls are stale — different corpus build, block TIDs differ; NOT a plugin delta) ✅ |
| structural asserts | check_allocas **160 passed, 0 failed** ✅ |
| semantics (-O0) | **32 PASS / 0 FAIL** ✅ |
| optimization-safety (opt -O2) | **32 PASS / 0 FAIL** ✅ |
| instrumentation blocker | clean (exercised by both builds) ✅ |
| plugin provenance | bundle sha16 `a99b6da6539dfa01`, provenance rewritten after the control/candidate installs ✅ |

GOTCHA re-hit this session: `dune install` FAILS on the bare switch
(mandir/docdir unknown) and silently leaves the OLD plugin installed —
always `eval $(opam env)` first, then verify the installed `.cmxs` hash
against `_build/install`'s (the provenance record carries it).

Artifacts: `/home/tovpr/nogates-battery/{emit,ctrl,sem,semopt}`.

**Last verified: 2026-09-09 EEST — SP-ONLY STACK SEMANTICS lane (branch
`sp-only-stack-semantics`, ADR 0008; code tickets 01-07 + doc ticket 08) —
BATTERY GREEN at `f206faf`, the fp-as-ordinary-GPR conversion complete**

The lane (ADR 0008, spec `.scratch/sp-only-stack-semantics/spec.md`):
**SP is the only register granted stack semantics by fiat.** RBP/fp is an ordinary
callee-saved GPR; its stack-ness is PROVEN (the value-based VSA tag), never assumed
by name. GATES: none — the emission inspects nothing (no shape checks, no
base-name tests, no spill rule). The key deletions: the `Abi.fp` field + `is_fp`/
`is_stack_reg` (RBP joins `callee_saved`), `fp_anchor`'s invented entry binding,
and the whole 32-bit spill apparatus (`u32_slots_of_sub`, `cast_source_width`,
`has_32bit_extract`) — SFLOAT now emits `sitofp` at the operand's own LLVM type.
NEW: the static model-interface table `fp_op_inputs` — the mapped intrinsic name
IS the interface fact; `create_native_fp_call` resolves operands from the block's
`intrinsic:xN` temps, never a sig-table fallback. Escape survived as a measured
necessity (`frame_escapes` SP-seeded closure + tag-gated `frame_addr_alias`); the
`-O2` corpus lane (`compile_corpus.sh <out>-o2`) is the class the lane serves.

| gate (at `cedbb62`, the code tip) | result |
|---|---|
| unit suite | **516 ok / 0 FAIL** (the 4 fp-gpr pins are genuine by-construction: `:u64`→`sitofp i64`, `31:0`→`sitofp i32`) ✅ |
| `dune runtest` (incl. referee) | **ALL PASSED**, clpequiv **2,861,148 / 0 mismatches** ✅ |
| both profiles build | default + vsa-debug **rc=0** ✅ |
| corpus emission (-O0) | **32/32 rc=0** (guarded = the 2 Unbounded knowns, identical to red3) ✅ |
| IR vs red3-o0 | **29/32 byte-identical**; the 3 deltas are the single SFLOAT lane (trunc+sitofp-i32 → sitofp at the operand's own type, mixed_fp_int/union_overlap/va_arg_mixed) — semantically proven ✅ |
| structural asserts | check_allocas **160 passed, 0 failed** ✅ |
| semantics (-O0) | **32 PASS / 0 FAIL** ✅ |
| optimization-safety (-O0 IR, opt -O2) | **32 PASS / 0 FAIL** ✅ |
| -O2 corpus (T07, `<out>-o2`) | PIE-clean 32 bins; emission 32/32 rc=0; allocas 159/1 (out_struct, shape-d); semantics 24/8 — the -O2 class, same eight vs the pre-lane plugin, NOT a lane regression (see the lane verdict, git history) ✅ |
| instrumentation blocker | clean (only `#ifdef VSA_DEBUG` diagnostics) ✅ |

Artifacts: `/home/tovpr/sp-battery/{t06-o0,t06-o2,sem-t06-o0,sem-t06-o2}`,
corpus `/home/tovpr/sp-corpus-o0` + the freshly built `/home/tovpr/sp-battery/corpus-test{-o2}`.

**Last verified: 2026-09-08 EEST — CLEANUP-9 LANE (branch `cleanup-9`, 17
commits: spec + tickets 01-09) — BATTERY GREEN, ≈ −2,400 LOC net, zero
intended behavior change; post-lane two-axis review verdict GO-WITH-FIXES
(docs-only fixes, landed on the SP branch)**

The lane (92 candidates in 7 lenses; spec in git history): 01 dead code,
02 word-ops twin fold (referee-gated), 03 pass-throughs + hoists, 04
constraint-lane merges, 05 ref→fold, 06 emitter dedup, 07 stack model, 08
tests + probes, 09 six file splits (hike filter/sections, fixture
harness/vocabulary, memmap Key, CLP core/arith, emitter
env/section/exp/mem/calls, VSA transfer/walk/driver). Every ticket landed
behind the full battery with corpus IR byte-identity vs its same-tree
control; two ticket items died by measurement mid-lane and are recorded in
their ticket files (the circular-hull merge — the lo>hi guard is the wrap
contract, S8/L3c3-1/R2-1/M5-1 pin it; the word-meet triple — the
check-free corners over width-polymorphic vars moved 3 binaries).

| gate (lane tip vs same-tree controls) | result |
|---|---|
| unit suite | direct-exe **507 ok, 0 FAIL**, suite output byte-identical across the test tickets ✅ |
| differential referee | clpequiv **2,861,148 checks, 0 mismatches** (incl. through the CLP seam shims) ✅ |
| corpus emission | **32/32 rc=0** on every ticket ✅ |
| IR byte-identity | **IDENTICAL 32/32** (out+err+rc+stdout) on every behavior-identical ticket ✅ |
| structural asserts | check_allocas **160 passed, 0 failed** ✅ |
| semantics (-O0) | **32 PASS, 0 FAIL** (last fully run at ticket 07; splits after it proven byte-identical) ✅ |
| optimization-safety (opt -O2) | subsumed by byte-identity where IR is unchanged ✅ |
| unmapped FP intrinsics | **0** (the 26-row table pinned by the emission wing throughout) ✅ |
| instrumentation blocker | **clean** (both profiles build) ✅ |

Known lane hazards for the next session: `/tmp` filled 100% mid-lane
(build/link temp) — heavy battery dirs now go on home disk with
`TMPDIR` set and worktree `--build-dir` off `/tmp`; the shared opam
plugin slot is install-serialized (per-worktree `dune exec` builds
never consult it).

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
dune exec zz_scratch_probe/stage_timer.exe    -- "$B"          # per-stage wall-time breakdown
dune exec zz_scratch_probe/conv_diag.exe      -- "$B"          # fixpoint non-convergence
# vsa-debug profile only:
dune exec --profile vsa-debug zz_scratch_probe/wbig_diag.exe -- "$B"
```

### Semantic harness (native-vs-lifted; the oracle)

The harness **never re-emits** — it operates on IR produced by
`run_corpus.sh`.  For a fresh-build validation, emit first, then run the
harness against the FRESH IR:

```sh
dune build @install && dune install                          # fresh plugin (see Build & test)
bash scripts/run_corpus.sh /tmp/corpus /tmp/emit             # emits out_*.ll
bash scripts/check_allocas.sh /tmp/emit                      # structural asserts
bash scripts/semantic/run_semantic.sh /tmp/corpus /tmp/emit /tmp/sem_out
```

Per binary it renames `@main`→`@hike_main` (and the crt1-colliding
`@_dl_relocate_static_pie`), `llc -O0 -filetype=obj`, links with
`harness.c` (plus `setjmp_stub.S` when the module uses setjmp/longjmp),
runs lifted vs native, and byte-diffs stdout.  Needs `llc` + `gcc`.

## Gotchas

- **The shared opam plugin slot is a cross-session hazard (hit twice,
  2026-09-07).** A parallel session can reinstall the plugin mid-lane; a
  reference emission may be lifted by the OTHER tree's plugin. Check
  `hike.cmxs.provenance` BEFORE consuming any emission;
  `record_provenance.sh` after every install. Per-worktree `dune exec`
  builds never consult the installed plugin.
- **A "surviving diagnostic" is not a passing gate (the 2026-09-02
  FP-table class).** The c484e13 merge silently dropped 11 of the 26
  `native_fp_op` rows; the degradation emitted CORRECT soft-float subs, so
  stdout stayed byte-identical and the battery stayed green — only an
  emission grep caught it. Grep the emissions for `unmapped intrinsic`
  when changing the FP-intrinsic table (the 26-row table is pinned at
  emission by the test_bil2llvm wing).
- **Same-address tagged defs: LAST-WINS (measured 2026-09-02, no unit
  pin).** 60-70% of tagged defs share an `Exp.equal` address with another
  def; `shape_of_addr`'s assoc-list find_map returns the LAST def in walk
  order. The corpus duplicates happen to AGREE (correct-but-accidental).
  If a same-address divergence bug surfaces, the pin to write: two
  Exp.equal-address defs, divergent tags (one singleton-Slot, one
  interval-Region), assert the later def's shape serves both. BAP facts
  (probe-verified): `Exp.hash`/`Exp.compare` exist; structurally-equal
  exps are NOT physically equal (no lifter hash-consing).
- **Region ids are an ordered partition (the re-baseline rule).**
  `merge_components` (sort-and-sweep) numbers `stack_rN` ascending in
  `(lo, hi, tid)`; ANY algorithm change renumbers regions corpus-wide and
  breaks IR byte-identity — a deliberate re-baseline session, never a
  rider.
- **`dune install` FAILS on the bare switch** (mandir/docdir unknown) and
  silently leaves the OLD plugin installed — always `eval $(opam env)`
  first, then verify the installed `.cmxs` hash against `_build/install`'s
  (the provenance record carries it).
- **Emitter fixture grammar (test_bil2llvm.ml, 2026-09-07):** hand-built BIR
  that the EMITTER consumes must be CFG-honest, unlike dce/vsa fixtures:
  (1) every `Goto`/`Call ~return` target must be a REAL block of the sub —
  `Blk.Builder.create` mints its own tid, so build the target block FIRST and
  use `Term.tid blk_result` (a fresh `Tid.create ()` dangles and dies in
  `bb_find_exn`/`blk_llvals`); (2) a conditional is cond-`Goto` +
  fallthrough-`Goto` (a `Ret` carrying `~cond` is not a branch —
  `create_branches` calls `goto_label_exn` on the second jmp); (3) the
  terminal `Ret (Direct tid)` never resolves its label (safe to mint fresh);
  (4) mapped-intrinsic call targets are `Tid.for_name "intrinsic:<name>"`
  (round-trips as `@intrinsic:<name>`; `fp_intrinsic_name` strips the `@`);
  (5) `capture_stderr` asserts on STDERR — hold the IR in a ref if a check
  needs both (the helper returns the captured text, not the emission).

## Agent skills

### Issue tracker

Local markdown issues under `.scratch/` (lane dirs: spec + tickets + verdict).

### Triage labels

Default five-label vocabulary: needs-triage, needs-info, ready-for-agent,
ready-for-human, wontfix.

### Domain docs

Single-context layout: one CONTEXT.md + docs/adr/ at repo root.
