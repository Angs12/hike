# Ticket 01 — sort-and-sweep `merge_components` + partition fixture

## Change

Replace `merge_loop` + `components_overlap` (`hike_stack_model.ml:343-374`,
inside `regions_of_sub`) with a named private `merge_components`:

```ocaml
(* Connected components of the interval-overlap graph, by sort-and-sweep.
   Sort by (lo, hi, tid); sweep with a running max-hi; a range joins the
   current component when its lo <= max-hi (it then overlaps some member,
   namely the one holding max-hi). Deterministic: the (lo, hi, tid) order
   fixes member order and component order, so ids are stable run-to-run. *)
let merge_components
    (items : (tid * (int64 * int64)) list)
    : (tid * (int64 * int64)) list list = ...
```

Sweep detail: sort ascending on `(lo, hi, tid)`. For each item j: if
`lo_j ≤ max_hi` of the component being built, append j (member order = sort
order) and `max_hi ← max(max_hi, hi_j)`; else close the component, start a new
one at j. Components come out sorted by their minimum lo — ids assigned in the
downstream `Base.List.foldi` are then ascending in lo.

Legacy shape dies: `merge_loop`, `components_overlap`, the `List.nth` access,
the per-event rescan, the member-pair `List.exists` (`exists_17538`).

## Fixture

New test in `test_cbat/test_regression.ml` beside R12-8/8b (the same BIL-builder
pattern): a designed overlap shape —
`[-64,-48], [-32,-32], [-40,-24], [-16,-16], [32,40]` over five defs — pinning
THREE regions with spans `(-64,-24)`, `(-32,-32)` … careful: `[-40,-24]`
overlaps both `[-64,-48]`? No: `overlap(lo1,hi1,lo2,hi2) = lo1≤hi2 && lo2≤hi1`.
`[-64,-48]` vs `[-40,-24]`: `-64 ≤ -24 ∧ -40 ≤ -48`? No → disjoint. So the
expected components are `{[-64,-48]}, {[-32,-32],[-40,-24],[-16,-16]}`? Check
`[-32,-32]` vs `[-40,-24]`: `-32 ≤ -24 ∧ -40 ≤ -32` → true → merge.
`[-40,-24]` vs `[-16,-16]`: `-40 ≤ -16 ∧ -16 ≤ -24`? `-16 ≤ -24` false →
disjoint. Hmm — so `[-16,-16]` is alone. Expected: components
`{[-64,-48]}`, `{[-32,-32],[-40,-24]}`, `{[-16,-16]}`, `{[32,40]}` — 4 regions.
The fixture asserts the partition (spans and member tids per region, as sets),
NOT ids: ids are the deliberate renumbering surface.

## Verification (ticket-local)

- `dune runtest` — green with the new fixture; existing R12-8/8b unchanged
  (they assert spans/partition, not ids — verify they pass untouched).
- Full battery from the worktree (emissions will differ from the c46454a
  control ONLY in stack_rN numbering — the ticket-02 diff review checks
  exactly that):
  - `bash scripts/run_corpus.sh /tmp/corpus /tmp/opencode/rm1-em`
  - `bash scripts/check_allocas.sh /tmp/opencode/rm1-em`
  - `bash scripts/semantic/run_semantic_all.sh /tmp/corpus /tmp/opencode/rm1-em <out>`
  - `bash scripts/semantic/run_semantic.sh ...` (8-bin)
  - `bash scripts/semantic/run_semantic_opt.sh ...`
- Build the plugin and install per AGENTS.md (`dune build @install && dune
  install`, `bapbundle remove hike` if a legacy bundle exists,
  `bash src/record_provenance.sh`), run gates with the fresh plugin.
