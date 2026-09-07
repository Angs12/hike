# Cleanup-8: escapable static facts — spec

Status: grilling-settled 2026-09-06, 3 rounds (Q1 lane=f8-cleanup; Q2-Q6
shapes; Q1-Q3 round-3 risk/scope/order). All measurements from
`.scratch/perf-profile/profile-2026-09-05-coreutils.md` and this session's
probes (f8census, passcost, stlbench, kbbench, termfind — the latter four
were throwaway; f8census stays in `zz_scratch_probe/`).

## Goal

Eliminate recomputed static facts and dead interface surface in the pass
pipeline (review finding 8 + finding 5's dead fields), measured against the
coreutils corpus (103 bins, 803 s serial). This is a cleanup lane: its
ceiling is ~1-2%/binary (DCE) plus locality/interface wins. It does NOT
replace the big lanes (rc_blocks hoist: 5-14%; word substrate: 31.6%).

## Settled decisions

| decision | answer |
|---|---|
| tickets | 01 dead fields, 02 VLA transport, 03 ABI sweep, 04 DCE worklist |
| to_graph x3 emitter | **SKIPPED by decision** (0.058 s/binary = 0.3%; recorded non-finding) |
| DCE shape | def-tid adjacency worklist, `keep` unchanged, affected-defs-only used-sets |
| DCE fallback | **all-or-nothing** — no no-op-fast-path fallback ticket |
| ABI rule | swap-not-add: `~target` → `~abi` where only ABI facts are read; `~target` stays where non-ABI target facts are read |
| VLA field | `vla_alloc_tids : Tid.Set.t` in `Convutils.vsa_info` |
| VLA guard | the `vla_bounds` fold guards on `alloc_tids = []` (same edit-site neighborhood) |
| fixture | dropping `refine_edge ~stores` edits F1-B4's one line in `test_properties.ml:1059` (accepted) |
| acceptance | full battery + **IR byte-identity 35/35**; `equal_vsa_info` grows a `Tid.Set.equal` arm (fallback: don't compare the field — decided during implementation) |
| parallel work | the word-substrate session's files (`cbat_word*`, `clpequiv`, `census`, `wordbench`, `wordequiv`, `src/cbat_vsa/dune`'s module additions) are left strictly alone |
| spec home | `.scratch/cleanup-8/` |

## Tickets

- `01-dead-fields.md` — zero-risk removals, first (shrinks later diffs)
- `02-vla-transport.md` — one fact, one producer; `vsa_info` carries it
- `03-abi-sweep.md` — swap-not-add across 4 files + emit_ctx fields
- `04-dce-worklist.md` — the only genuinely subtle item, last

## Measured non-findings (recorded so nobody re-proposes)

| claim | measured | verdict |
|---|---|---|
| KB transport (2,800 tx/binary) | 0.001 ms/call, 3 runs stable | dead as speed; the join machinery is a clarity question only |
| stl recomputing the stack model for non-Range subs | 0.002 s/binary (123 subs reach it; `has_mem_ops` short-circuits the rest) | dead |
| `Abi.of_target_opt` as a speed item | 0.17 µs/call → ~1 ms/binary | dead as speed; alive as interface honesty (ticket 03) |
| `vla_bounds` empty-walk alone | 0-1 VLA subs per binary | subsumed by ticket 02's guard |
| `Sub.to_graph` ×3 in the emitter | 0.058 s/binary (0.3%), NOT O(1) (`of_sub` fold + DFS per call) | skipped by decision |
| per-visit `Solution.create` snapshot | O(1) — boxes the existing map (`graphlib_graph.ml:1239`) | non-finding |
| `Program.lookup blk_t` in the transfer | Hashtbl path cache, O(1) | non-finding |
| Transfer_memo as a precision-preserving win | 1.1-7.1% hits, 29-58% stale (6 heavy subs, 2 binaries) | the memo is near-pure overhead today — out of this lane's scope, feeds the fixpoint-lane grilling instead |
| `Term.find blk_t sub n` per walk pop | 1,273-1,924 ns vs 67 ns map lookup; 0.33-0.51 s/heavy sub; 5-14% of corpus | **real but SHELVED** — the rc_blocks lane, not this ticket |

## Order and gating

01 → 02 → 03 → 04, each landing independently green, one full battery at the
end of 04. 02's record-shape change is the only one that touches the KB
slot's compared value — run the battery after it too (cheap: the lane's
commits are small).
