# Ticket 01 — dead fields and dead parameters

Status: landed as 085f378 (2026-09-06). Zero risk, no behavior change, lands first (shrinks
the diffs of 02-04).

## Items (all verified zero-read on main @ 753601b)

1. **`analysis_ctx.blk : blk term option`** — `cbat_vsa.ml:1570`; constructed
   at 2064 and 2213, never read. Also removes the `~blk:(Some b)` threading.
   The record is exported at `cbat_vsa.mli:115-121` — shrink the `.mli` type.
2. **`edge_cond.cond_of_edge : jmp term`** — `cbat_vsa.ml:2112`, built at
   2132, never read (only `acc_cond` is consumed at 2304). Retains a whole
   jmp term per edge of every sub for the sub's lifetime.
3. **`refine_edge ~stores`** — `cbat_vsa.ml:1480`, bound never used (the real
   store path is `analysis_ctx.stores` → `known_nonneg_of`). Exported at
   `cbat_vsa.mli:149-156`; **edit the F1-B4 fixture line**
   `test_cbat/test_properties.ml:1059` which passes
   `~stores:(Some (Vsa.stores_of_sub sub))` (settled: accepted).
4. **Replay-arm dead args** — `cbat_vsa.ml:2672-2673`: `~sol:(Some sol_snap)`
   and `~edge_conds:(Some edge_conds)` passed to a `denote_block_with_stores`
   call under `no_walk:true` ⇒ `discarded = true` ⇒ `refine_edge_inline`
   returns at 2231 before touching either. Drop both from THIS call only
   (they stay optional params for the real calls).
5. **`analysis_ctx.sub : sub term option`** — `cbat_vsa.ml:1569`, read only
   at 1998 as a boolean (`Some { sub = Some _; _ } -> env`). Change the field
   to `bool` (or keep the option and drop the payload — pick the bool; it
   gates `inverse_denote_exp`, name it for what it means: production-mode).
   Touches the same fixture family as item 3 — update construct sites 2064,
   2213.
6. **`Cbat_wto.pp_comp`** — `cbat_wto.ml:35-40`, exported `cbat_wto.mli:30`,
   zero callers repo-wide. Delete from both.
7. **`Stages.bump_walk_pops` args** — `cbat_vsa.ml:1542-1549`: the argument
   list (`~blocks:(Core.Set.length !r)` etc.) is evaluated per walk to feed
   a production no-op. Make the prod adapter's args lazy (unit-passing
   closure) or hoist the evaluation under `#ifdef VSA_DEBUG` — the debug
   build keeps exact reporting.

## Verification

- `dune build` (both profiles) — the `.mli` edits compile every consumer.
- `dune runtest` — the F1-B4 fixture edit is the only test-file change.
- Corpus emission + IR byte-identity 35/35 (nothing here can move bytes, but
  the bar is cheap and the lane runs it after every ticket anyway).
- Probes build: `vs a_debug.exe`, `wbig_diag.exe` reference `refine_edge`'s
  signature via `Hike` — check `zz_scratch_probe/` for `~stores` uses before
  editing (grep first; the parallel session's files are OFF-LIMITS:
  `cbat_word*`, `clpequiv`, `census`, `wordbench`, `wordequiv`, and
  `src/cbat_vsa/dune`'s module list).
