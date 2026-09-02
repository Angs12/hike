# diag-channel — principle #6 as compile-time elimination + the dune-built plugin

**Status:** implemented on branch `diag-channel` (worktree `/tmp/opencode/wt-diag`),
2026-09-03, off main `40955da`.
**Depends on:** nothing (self-contained; disjoint files from `battery-merged`).
**Blocks:** the stale-plugin class (the 2026-09-02 poison-phi incident);
the bapbuild-doesn't-see-dune pipeline split; every future "just add a
debug print" relapse.

## The user directive

> The instrumentation should not be compiled in the production binary!

and, when bapbuild's parallel pipeline broke on the new `#ifdef` syntax:

> You can move out of using bapbuild and bapbundle and move the plugin
> building to dune entirely! It is the best way!

## The grilling record (17 questions, the settled tree)

| # | Decision | Answer |
|---|---|---|
| Q1 | Where is the line? | ANY runtime-variable behavior is debug; production emits fixed diagnostics only |
| Q2 | Enforcement | Build-time blocker in dune |
| Q3 | Debug-path friction | Make vsa-debug cheap so there's no excuse |
| Q4 | Provenance | Lives in the build/install step, not production code |
| Q8 | Provenance scope | + always-clean builds (the stale-CACHE class is invisible to source identity — measured: identical sources shipped 22 poison phis) |
| Q9/Q14 | Mechanism | cppo (`#ifdef VSA_DEBUG` lines, `-D` by `%{profile}`) — ppx_optcomp is DEAD here (no `-D`; `[%import]` fails in dune's ppx sandbox) |
| Q10 | The price | The `hike:` family is the only production channel; a vsa-debug rebuild is the cost of developer tracing |
| Q11 | Triage | Delete noise, gate the valuable (confirmed list below) |
| Q12 | Checkable rule | One sanctioned output channel; ban direct prints elsewhere |
| Q13 | Build cheapness | Fix as part of this work |
| Q16 | Triage list | As proposed |
| Q17 | Ergonomics | `--build-dir` opt-in (zero default tax; the two-context workspace taxes every default build) |
| — | llvm dynlink blocker | In-repo rule + install backfill (bapbundle's own recipe, byte-identical) |

## The mechanism (all experiment-verified before implementation)

- **cppo before ppx-jane.** `ppx-jane` IS the old `pps ppx_bap` driver —
  it regenerates `[@@deriving equal]`'s `equal_vsa_kind` from the type;
  removing it broke convutils.ml. cppo (line-level, in the switch) runs
  FIRST, feeds the driver via `-impl -`; `-D VSA_DEBUG` is passed only
  when `%{profile}` = vsa-debug. `.mli` inputs get `-intf`.
- **The blocker** (`src/check_instrumentation.sh`): python-inside-bash,
  COMMENT-AWARE (OCaml comments stripped before matching — the first
  version false-positived on its own doc text), `#ifdef VSA_DEBUG`
  regions skipped, `hike_diag.ml` exempt as the channel. Aliases `all`
  + `install` (`alias default` does NOT fire the rule — verified).
- **Debug builds:** `dune build --build-dir _build-debug --profile
  vsa-debug`. Without a separate dir, every profile switch is a FULL
  10-22s rebuild in both directions (measured; no shared cache: 0B).
- **The plugin stanza:** `(plugin (name hike) (libraries hike) (site
  (bap-common plugins)))` + `(using dune_site 0.1)` in dune-project.
  bapbuild dies on the cppo syntax (`Syntax error` at the raw `#ifdef`,
  hike.ml:662) — proof the two pipelines could never coexist.

## The llvm backfill (the one blocker dune could not express)

The `llvm` opam package ships NO `llvm.cmxs` and NO findlib META — a
dune-built plugin dynlinking Llvm symbols fails
(`hike.cmxs: undefined symbol llvm_int64_of_const`). bapbuild hid this
by packing a self-built llvm.cmxs INTO the bundle zip. The backfill
script reproduces bapbundle's recipe EXACTLY
(`ocamlopt -shared -linkall llvm.cmxa libllvm_*.a` — byte-identical
501008 bytes) and installs it + a META into the switch's `lib/llvm/`.
Idempotent (cmxs newer than cmxa → skip), loud on failure.

Gotcha: remove the legacy bundle (`bapbundle remove hike`) or bap loads
BOTH plugins and dies (`Hashtbl.add_exn got key already present hike`).

## The site map (what moved where)

| Site | Fate |
|---|---|
| hike.ml:264-266, 469-471 (section min/max/len) ×2, 462 (named region) | DELETED (noise) |
| hike.ml:478-482, 547-551 (Creating data/rodata/bss/got/gotplt/rodata_rel), 559 (Getting symbols) | DELETED |
| hike.ml:418 (Skipping sub — filter pass) | DELETED |
| hike.ml:598 (Warning: section not found) | → `Hike_diag.warn` |
| hike.ml:674, 694, 714 (vsa guard/vsa/stl tag counts) | `#ifdef VSA_DEBUG` |
| hike_stack_to_locals.ml:578, 586-591 (member-NOT-direct, region dump) | `#ifdef VSA_DEBUG` (the valuable forensics) |
| bil2llvm.ml:523 (create_load DYN per-hit dump) | DELETED |
| bil2llvm.ml:622, 1087, 1879, 2467 (undef-read ×2, guarded ×2) | → `Hike_diag.warn` (format text verbatim) |
| bil2llvm.ml:968 (fallback-lo dynamic) | `#ifdef VSA_DEBUG` |
| bil2llvm.ml:2335, 2341, 2347 (per-sub emission traces) | DELETED |
| hike_vsa.ml:322 (not converged), 355 (100%-invariant gap) | → `Hike_diag.warn` |
| cbat_vsa_utils.ml:27 (not_implemented stderr duplicate) | DELETED (Event.Log keeps it; nothing greps stderr for it — corpus err_*.txt verified) |

## Acceptance (all measured 2026-09-03)

- **IR byte-identical to the main 40955da control, 32/32** — every
  deletion/gating/migration changed zero emitted bytes.
- Unit suite: 467 ok / 0 xfail / 0 XPASS / 0 FAIL (the strict harness
  passes OUTRIGHT — 0 XPASS is what "honest + clean" looks like).
- Corpus 32/32 rc=0; check_allocas 160/0; semantic-all 30/2; opt 30/2;
  8-bin 8/8; unmapped intrinsics 0; probes pass, 0 crashes.
- Blocker red path verified: injected `Sys.getenv_opt` → rc=1 both rules.
- Compile-out proven by artifact grep: production `*.pp.ml` → 0 forensics
  hits; `_build-debug/*.pp.ml` → 1 each.
- The dune-built plugin lifts and emits through the site dir
  (`bap-common/plugins/hike/META`, `requires = "hike"`), with
  `hike: section 5 was not found in binary` firing through Hike_diag —
  the migrated warning, live, in the real pass.

## Open follow-ups

1. **Rebase when main's mid-merge resolves** (main's test_cbat.ml carries
   14 unresolved `<<<<<<<` markers as of 2026-09-03; this branch is off
   the pre-conflict 40955da) and re-run the unit suite against the
   reconciled count.
2. **Merge with `battery-merged`** (2026-09-02: battery driver + the
   three-gate semantic collapse) — disjoint files; the battery's
   stale-plugin step should gain the provenance verification.
3. The orphaned probe drivers (`defsize.ml`, `passcost.ml` — unbuildable,
   no dune stanza, someone's in-flight work) still need wiring into
   vsa-debug or deletion; NOT touched by this branch (untracked files).
