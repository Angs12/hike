# T2 — the simplification pass (P1)

Spec: `.scratch/typed-model/spec.md` (binding constraints apply).
Blocked-by: none. Blocks: nothing (independent sweep).

## Scope

Sweep everything the recent removals orphaned — the typed-frame
generalization (ticket 04, `--hike-stack-model` parameter deleted,
`create_inttoptr` → `create_addr_ptr`), ADR 0003 (restriction/relevance
deleted), the sp-only lane (ADR 0008, fp deleted), and the
simplification program's file splits left behind:

- dead values (e.g. `equal_int64_pair` — verify then delete), dead
  constructors, dead fixture builders (a `mk_*` builder with no caller
  is deleted like any dead code — test honesty rules),
- stale comments mentioning DELETED machinery (the deleted parameters,
  passes, tags, env toggles, bapbuild/bapbundle rituals),
- mli over-exposures (names exported but unused outside the module —
  unexport them; do NOT shrink the `Hike.*` Library Seam surface in
  `src/hike.mli` or the `Cbat_vsa.Test_seam` quarantine without a
  consumer-side check),
- dangling doc references: CONTEXT.md terms and AGENTS.md lines stay
  as they are (the owner maintains them); this ticket is CODE hygiene.

## Hard limits

- ZERO intended behavior change. If a deletion candidate is reachable
  from any production path, it is not dead — leave it and record why.
- Do NOT pre-delete things T3 will remove (`value_env`, the frame
  relation, `seed_frame`, `apply_frame_def`, `rewrite_addr` are T3's
  scoped deletions — touching them here only creates merge conflicts).
- The instrumentation blocker (`src/check_instrumentation.sh`) stays
  clean; do not add prints anywhere.

## Battery protocol (NO bap — you do not hold the shared plugin slot)

```sh
cd <your worktree> && eval $(opam env)
dune build                                   # default profile, all probes
dune build --profile vsa-debug zz_scratch_probe/vsa_debug.exe zz_scratch_probe/wbig_diag.exe
dune runtest                                 # ALL PASSED + referee 0 mismatches
```

NEVER `dune install`, never run `bap` (the shared opam slot belongs to
another agent this wave). The merger runs the full corpus battery on
the merged branch; your branch must be plausibly behavior-identical —
for every deletion, state the grep that proved no callers.

## Acceptance

- `dune runtest` green (both profiles build; referee 0 mismatches).
- A list in the verdict file: each deletion + the no-caller proof.
- Net LOC negative. No corpus-facing behavior change expected; if the
  merger's battery disagrees, the ticket reopens.

Worktree: `/home/tovpr/hike-t2`, branch `tm/t2-simplify`.
