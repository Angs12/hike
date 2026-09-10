# S10b — verdict: the convutils split (items 9 + 11); the drawer is GONE

Landed 2026-09-10 on `tm/s10b` (worktree `/home/tovpr/hike-s10b`), branched
at the tip `4402025`. Commits: `cfc8035` (item 9a — the Vsa record),
`58660e4` (items 9b–f — the emitter state + the dissolved residue).
`src/convutils.ml` is DELETED (430 lines → 0); the library is 29 files,
+772/−676 over two commits. Final provenance:
`git=58660e4 src=fb68c8ebe0f915ad bundle=45a6c34ca6db46cd`. Battery
artifacts: `/home/tovpr/tm-battery/s10b/`.

**ZERO behavior change, proven: corpus emission BYTE-IDENTICAL 37/37 on
BOTH lanes** vs `/home/tovpr/tm-battery/merge-t4b/emit-{o0,o2}` — per-file
`cmp` of `out_*.ll` AND `err_*.txt` (0 diffs of 37+37+37+37; directory
listings identical). Module moves are IR-invisible; var names (the only
IR-visible surface — `hike_window`, `hike_slotN`, `stack_rN`, `sp_slot`,
region/base names) are untouched by construction.

## 1. The move inventory (what went where, and why)

### (a) The Vsa record → `Hike_stack_model` (commit cfc8035)

`vsa_kind` (the `Cbat_extraction.kind` alias), `region`, `split_plan`,
`call_site`, `vsa_info`, their equalities, and the builders
(`mk_vsa_info_maps`, `mk_vsa_info`, `empty_vsa_info`) moved verbatim
into `hike_stack_model.ml` (as `module Vsa = … include Vsa` at the top,
preserving the block's compile environment).

**Why the model and not a dedicated `Hike_vsa_record`** (the ticket's
measure — delete the most indirection): the model is the record's
heaviest consumer (~50 qualified refs, all now unqualified) and the
producer/emitter CONTRACT point all three roles already reach — the
producer (`hike_vsa`) builds the record, the KB (`hike_kb`) stores it,
the emitter reads it. A dedicated module would have re-pointed every
qualifier 1:1 (zero deleted), added a module, and required a new mli
export — the opposite of the measure. Dependency directions stay
acyclic: `hike_kb`/`bil2llvm_env` gained edges INTO `Hike_stack_model`
(the model references neither).

Consumer re-paths, mechanical: `hike_kb` aliases `module Model =
Hike_stack_model`; `hike_vsa`'s existing `Model` alias covers it;
`hike_stack_to_locals` likewise; the emitter files re-path
type/constructor references to `Hike_stack_model.*` (their existing
style — `Hike_stack_model.arg_slot` was already there). Field
projections de-qualify ONLY where the record type is in scope (the
model itself; `Model.`-qualified elsewhere — the emitter files keep
`sub_info.Hike_stack_model.offsets`, an exact shape match of the old
`sub_info.Convutils.offsets`).

`hike.mli` re-exports the record through the `Stack_model` sig (types
with fields and constructors + the two `mk_*` builders + the five
equalities) — the seam's module set is unchanged; `Hike.Vsa`'s
`offsets_of_sub` return type re-paths. Tests and probes re-path
mechanically: test_common's `module Cu` (which test_fixtures resolves
through `open Test_common` — the alias was NOT orphaned, it re-points
to `Stack_model`), test_bil2llvm's own `Cu`, test_dce's direct paths,
and all eight probes (`Hike.Convutils.X` → `Hike.Stack_model.X`,
record members only).

### (b) The emitter state → `Bil2llvm_env` (commit 58660e4)

`emit_ctx` + `empty_emit_ctx` (with `stack_anchor`, the newest ctx
field, riding along), the WVar machinery (`wvar`, `wvar_of`, `WVar`,
`WVarMap`, `llvalue_map`, `blk_llvals`), the blk-llvals accessors
(`init_blk_llvals`, `insert_phi`/`get_phi`, `insert_local`/`get_local`,
`probe_local_family`, `clear_blk_llvals`/`clear_bbs`, `insert_bb`/
`get_bb`, `bb_find`/`blk_llvals_find`), `EHashtbl`, the sig helpers
(`add_sub_sig`, `get_args`/`get_rets`/`ret_set` + the internal
convention reader), the section types (`section`, `section_type`,
`section_type_to_string`), and the emitter-side BAP misc
(`goto_label_exn`, `label_tid`/`label_exp`, `call_exn`, `cf_type` +
`entry_blk_tid`, `is_empty`, `is_intrinsic_name`) moved into
`bil2llvm_env.ml` (77 → 354 lines). **Why**: the module already existed
for exactly this (the KB context vars, `emit_ctx_var`, `sub_frame`) and
every emitter lane ALREADY opens it — the moved names resolve through
those opens with zero textual churn; emit-ctx field projections
de-qualify (`ctx.sp`, type-directed).

The section types land here and not in `Hike_sections` because
`hike_sections` opens `Bil2llvm`, which opens `Bil2llvm_env` — a
model→prep edge would close the cycle `Bil2llvm_env → Hike_sections →
Bil2llvm → Bil2llvm_env`. The env module is the section-prep/emitter
boundary carrier (it holds `section_list_var`); the prep modules
reference it exactly as they referenced `Convutils` before.

### (c–f) The dissolved residue (each to its consumer)

| member | home | why |
|---|---|---|
| `is_mem` | `Hike_stack_model` | the var grammar lives there (S10a item 10: slot/window/region vars mint in the model); joins `is_region_mem`; all four consumers already depend on the model — zero new edges |
| `is_goto` | `hike_filter.ml` | sole consumer |
| `sanitize_name` | `Bil2llvm_env` + a `val` on `bil2llvm.mli` | the emitter owns the LLVM name minting (`hike_filter` already consumes emitter-owned intrinsic facts through the mli — same precedented direction); `hike_vsa`'s target-name map and the fixtures share the fact, so the mli re-export is the minimal shared surface |
| `is_intrinsic_name` | `Bil2llvm_env` | `hike_dce` consumes it library-internally (`Bil2llvm_env.is_intrinsic_name`), same class as the filter's emitter-fact consumption; no mli growth |
| window var (item f) | — | already dissolved by S10a item 10 (`hike_window_var` in `Hike_stack_model`); nothing left to move |
| orphans | — | none: every remaining convutils member had live consumers; the internal-only helpers (`bb_find`, `blk_llvals_find`, `get_calling_convention`, `wvar_of`, `llvalue_map`) moved with their callers |

With everything placed, `src/convutils.ml` is deleted and
`hike.mli`'s `module Convutils` re-export with it. `CONTEXT.md`'s
Library Seam line updated (it named `Hike.Convutils` — a live claim
now false). ADRs 0005/0008 keep their historical `Convutils.*`
references: point-in-time records, already stale pre-lane
(`is_positive_kind`/`Convutils.fp` died in T4/ADR 0008's own landing).

## 2. Item 11 — the hike_vsa split: measured, verdict SKIP

`hike_vsa.ml` is 389 lines post-T4 (78 pre-T4). The structure is
linear and each piece has one complete rule: singleton/shape helpers
(~35) → the CALLEE-side classifier `callee_side` (~72, one per-def
walk, per-arm comments) → `resolve_target` (~11, the seam member) →
the CALLER-side classifier `caller_side` (~120: site slot stores,
singleton resolution, escape extents) → the driver `offsets_of_sub`
(~125: fixpoint → extraction → `finish`, which builds the record
complete at one site — callee+caller facts, the storage lattice, the
plan fold).

The ticket's condition — "if the landed form keeps the promotion
classifier + tag extraction + the plan fold together IN WAYS THAT
STRAIN the module" — does not hold: the three concerns compose in ONE
`finish` closure (the record built complete at one site is the
architecture map's own principle), each classifier has exactly one
caller (inside `finish`), and the L1/T4b/S10a lanes already removed
the stale mass (k_ranges, superseded comments). Splitting the
classifiers out would add a module and an alias (indirection — the
opposite of this lane's measure) to separate the classifiers from the
record construction they exist to feed. Recorded not-done; re-open
only if the producer grows a second consumer-facing role.

## 3. Byte-identity proof

Fresh plugin install → `run_corpus.sh` over the prebuilt corpora
(`/tmp/corpus`, `/tmp/corpus_o2`; the -O0/-O2 canary re-checked:
byte_copy and fizzbuzz_safe DIFFER across lanes) → per-file `cmp`
against the T4b references:

| lane | out_*.ll | err_*.txt | dir listing |
|---|---|---|---|
| -O0 | 37/37 identical | 37/37 identical | identical |
| -O2 | 37/37 identical | 37/37 identical | identical |

## 4. Gate table (the final tree)

| gate | result |
|---|---|
| build, default + vsa-debug profiles | rc=0 both ✅ |
| instrumentation blocker | clean ✅ |
| `dune runtest --force` failure set | **== EXACTLY the 8 pre-existing** (E2eD-7/8, LM F1-B1×2, F1-B3, F1-FT×2, F1-NEQ); `runtest-c2.log` ✅ |
| referee | **clpequiv: checked=2,861,148 mismatches=0** ✅ |
| -O0 emission | 37/37 rc=0 ✅ |
| -O0 structural asserts | 185 passed, 0 failed ✅ |
| **-O0 byte-identity vs `merge-t4b/emit-o0`** | **37/37 IDENTICAL** (out + err) ✅ |
| -O0 strict semantics | **37 PASS / 0 FAIL** ✅ |
| -O0 strict opt-safety | **37 PASS / 0 FAIL** ✅ |
| -O2 emission | 37/37 rc=0 ✅ |
| -O2 structural asserts | 185 passed, 0 failed ✅ |
| **-O2 byte-identity vs `merge-t4b/emit-o2`** | **37/37 IDENTICAL** (out + err) ✅ |
| -O2 pinned semantics | **semantic-pin: OK — failing set == golden list (byte_copy, fizzbuzz_safe, jump_table_sw, spill_many, union_overlap, va_arg_mixed, va_arg_vacopy)**; no movement ✅ |
| provenance | src `fb68c8ebe0f915ad`, bundle `45a6c34ca6db46cd` (recorded after install) ✅ |

Battery summary: the single hard red is the `dune runtest` rc gate —
the pre-existing 8-failure baseline makes rc non-zero by design
(identical to the T4b/S10a/typed-removal records). Everything else
green. No pin movement, no golden-list change, no IR change.

## 5. Hazards hit (for the record)

- **ppx-jane's parser rejects `{ e with f = … }` when `e` is an bare
  application** (`{ empty_emit_ctx () with … }` → `Syntax error: "}"
  expected` at `with`; plain `ocaml` accepts it — only the
  cppo→ppx-jane pipeline trips). The parenthesized form
  `{ (empty_emit_ctx ()) with … }` is required — the original
  `(Convutils.empty_emit_ctx ())` had the parens for this reason.
- Unqualified record-field projections (`sub_info.offsets`) do NOT
  resolve by type direction alone when no in-scope module exposes the
  field — files that do not open/alias the defining module must keep a
  qualified path (`sub_info.Hike_stack_model.offsets`). Only
  type-in-scope sites (the model itself) de-qualify fully.
- One move transcription dropped `cf_type`'s FUNCTION body (the type
  moved, the value was missed) — caught by the build (`Unbound value
  cf_type`), restored verbatim. Both profiles + runtest cover the
  moved surface.
