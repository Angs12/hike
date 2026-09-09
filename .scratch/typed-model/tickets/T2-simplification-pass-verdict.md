# T2 verdict — the simplification pass

Branch `tm/t2-simplify` (worktree `/home/tovpr/hike-t2`), commits
`b97ea00` (dead values), `250f86c` (unexports), `364863d` (comments).
Base: `775d616`. Ticket: `T2-simplification-pass.md`; spec §T2.

**Net LOC: -41 on tracked code (12 insertions / 53 deletions; the
insertions are the comment rewrites).** All deletions are
zero-caller-verified; zero intended behavior change (nothing on any
production or emission path changed except comment text).

## Deletion inventory + no-caller proofs

Proof form: `/usr/bin/grep -rn -w <name>` over `src test_cbat
zz_scratch_probe` (GNU grep; the `grep` shell function here wraps
ugrep and must not be trusted for scans) — after excluding the
definition, zero references remain. The sweep tooling is committed
next to this verdict (`deadscan.sh`, `mli_scan.sh`, `mli_scan2.sh`,
`depth_trace.sh`).

### Dead values (deleted; commit b97ea00)

| name | home | proof |
|---|---|---|
| `Convutils.equal_int64_pair` | `src/convutils.ml` | definition-only; never referenced in any .ml/.mli, incl. its own module (`equal_vsa_info` uses `equal_vsa_kind`/`equal_region`, not this) |
| `x86_64_target` | `test_cbat/test_common.ml` | no caller in any test module (single flat test executable); its own comment ties it to the NAME-granted fp fixtures deleted by ADR 0008 — deleted with its comment |
| `r5_cardn_gt` | `test_cbat/test_properties.ml` | no caller; deleted with its comment. `Cbat_word.gt_int` itself STAYS (production: `cbat_clp_set_composite.ml:64,67`; test: WO7) |
| `dump_frame` | `zz_scratch_probe/audit02.ml` | no caller in the legacy probe; `ws_str`/`exp_str` stay (`audit_sub` uses them) |
| `Cbat_word.hash` (def + `val`) | `src/cbat_vsa/cbat_word.ml/.mli` | zero callers tree-wide (only `Z.hash` false positives); no functor application over `Cbat_word` exists (`grep -E "(Make|Make1)\s*\(?\s*Cbat_word"` = empty), so the `Hashable`-style surface is unneeded |

### mli over-exposures (unexported; values STAY; commit 250f86c)

| export | home | proof |
|---|---|---|
| `Cbat_word.to_z` | `cbat_word.mli` | 26 internal uses, zero references outside `cbat_word.ml` |
| `Cbat_word.of_z` | `cbat_word.mli` | internally alive (`of_int64`), zero external references |
| `Test_seam.stores_of_sub` | `cbat_vsa.mli` + the `let stores_of_sub = stores_of_sub` alias in `cbat_vsa.ml` | no production/test/probe consumer; the value stays (`static_graph_vsa` uses it at `cbat_vsa.ml:136`) |

Not touched without consumer proof: `src/hike.mli` (checked — every
module and `copy_reloc_slots` are consumed, incl. `test_regression.ml`),
`Bil2llvm.mli` (every export consumed), all other `Cbat_*` mli exports
(`mli_scan.sh`: zero dead exports), `Test_seam`'s remaining names
(each has a test consumer).

### Stale comments naming deleted machinery (text-only; commit 364863d)

| site | was | now |
|---|---|---|
| `src/bil2llvm.ml` (`populate_blks`) | `(* 32-bit FP spill slots, computed once per sub. *)` above plain block emission | deleted — the ADR-0008 apparatus is gone |
| `src/bil2llvm_exp.ml` (`create_load` non-const arm) | "Non-constant addresses use inttoptr" (the pre-typed-model rule) | describes `create_addr_ptr` routing (frame GEP vs foreign inttoptr) |
| `test_cbat/test_bil2llvm.ml` Family 7 | present-tense description of the deleted `u32_slots_of_sub` / `Abi.is_fp` / `cast_source_width` "width bug" path, in header, fixture comment, and two inline lines | describes the current by-construction width rule (header, fixture comment, two inline lines rewritten) |
| `test_cbat/test_vsa.ml` (D7-15 block) | "Restriction stays OFF: ON would skip the untagged cast" — no such switch exists since ADR 0003 | states the current no-gates fact (every def denoted, test non-vacuous) |

## Gates (run on the exact committed tree)

| gate | result |
|---|---|
| `dune build` (default profile; the instrumentation blocker runs on `alias all`) | rc=0 (only the pre-existing `Of_stringable_without_uuid` alert on an untouched line) |
| `dune build --build-dir _build-debug --profile vsa-debug zz_scratch_probe/vsa_debug.exe zz_scratch_probe/wbig_diag.exe` | rc=0 |
| `dune runtest` | failure set IDENTICAL to the pristine-tip baseline measured before any change: the 8 pre-existing (E2eD-7, E2eD-8, LM F1-NEQ/FT×2/B3/B1×2); the ok-line set byte-identical |
| clpequiv referee | `checked=2861148 mismatches=0 both-raised=1300` (identical to baseline) |

No `dune install`, no `bap` (per the ticket protocol — the shared
plugin slot belongs to another agent). The merger's corpus battery is
expected to be behavior-identical: no deleted name had a caller, and
the emitter/producer paths changed only in comments.

## Deliberately LEFT (with reasons)

- **T3's scoped deletions** — `value_env`, `seed_frame`,
  `apply_frame_def`, `frame_add_fvar`, `mentions_frame_var`,
  `rewrite_addr`, `frame_of_state`, the whole frame relation: alive and
  consumed; deleting them here would only create merge conflicts.
- `cbat_transfer.ml` "the restriction gate is deleted" comment —
  describes the CURRENT no-gates state, kept.
- `test_cbat/test_domains.ml` "wrapped spill" comments — describe the
  Mem map's word-wrap semantics, not the deleted spill-slot apparatus.
- `scripts/record_provenance.sh` / `src/backfill_llvm_cmxs.sh`
  bapbuild/bapbundle mentions — accurate records of the current
  dune-only flow ("bapbuild retired", "bapbundle's own recipe").
- `precision_probe.ml`'s `HIKE_VSA_DIAG_BOTTOM` env read — the
  AGENTS-sanctioned test/probe-only toggle.
- The vendored `cbat_clp_arith.ml` TODO comments — upstream CBAT text.
- The alternating `(*doc *))` + `;` + `(  let ... ())` block style in
  the test files — odd but LIVE code: a paren/comment depth trace
  (`depth_trace.sh`) shows every block executes and the file balances;
  reformatting is churn, not hygiene.
- AGENTS.md's debug-exe list still names `edgemulti_probe`, which has
  no dune stanza — AGENTS.md is owner-maintained; recorded here for
  the owner instead.
