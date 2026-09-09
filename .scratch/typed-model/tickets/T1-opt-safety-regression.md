# T1 — the typed-model opt-safety regression (P0)

Spec: `.scratch/typed-model/spec.md` (binding constraints apply verbatim:
NO GATES, NO FALLBACKS, soundness over precision). Blocked-by: none.
Blocks: T3 (same emitter code region; the program's ordered head).

## The failure (measured)

`nested_struct` and `struct_by_value`: unoptimized lifts are CORRECT
(semantics 33/33), but after the consumer's optimizer (`opt-21 -O2`)
their behavior DIVERGES from native. Strict opt-safety gate
(`scripts/semantic/run_semantic_opt.sh`) = 31 PASS / 2 FAIL on the
typed reference emission `/tmp/emit_typed_o0`. The offset-model
emission `/tmp/emit_l1_o0` was opt-green for both — the IR delta
between the two emissions for these two binaries is the primary lead.

Known dead ends (do NOT re-run): the align-1 hypothesis (frame-routed
accesses claiming natural alignment) was TESTED and REJECTED — the
violations persist with byte alignment. The failing set is stable
across runs (not garbage-dependent). The gate's built-in single-pass
auto-bisect exonerates EVERY single pass → the miscompile needs a pass
COMBINATION; next diagnostic is per-PAIR bisection (e.g. `-O2` minus
{sroa,mem2reg}, {sroa,early-cse}, … pairwise) plus the IR delta vs
`/tmp/emit_l1_o0`.

## The mandate

The fix must be the GENERAL address-materialization rule — the one
rule every access goes through (`create_addr_ptr`,
`src/bil2llvm_mem.ml` and its callers) — never a per-shape patch, never
a guard. Every emission rule stays complete per tag kind (spec user
story 8). A diagnosis that ends in "arm X assumed impossible" must fix
the assumption at the rule, not special-case the shape.

## Battery protocol (SHARED-SLOT — you are the only bap user)

This ticket REQUIRES emission-level iteration, so you hold the repo's
single opam plugin slot for the whole wave: no other agent will run
`bap` or `dune install` concurrently.

```sh
cd <your worktree> && eval $(opam env)
dune build @install && dune install     # your plugin into the shared switch
bash src/record_provenance.sh           # REQUIRED after every install
bash scripts/run_corpus.sh /tmp/corpus /tmp/emit_t1
bash scripts/check_allocas.sh /tmp/emit_t1
bash scripts/semantic/run_semantic.sh /tmp/corpus /tmp/emit_t1 /tmp/sem_t1        # strict: 33 PASS / 0 FAIL required
bash scripts/semantic/run_semantic_opt.sh /tmp/corpus /tmp/emit_t1 /tmp/semopt_t1 # 33 PASS / 0 FAIL required (now 31/2)
```

Reproduce first: re-emit fresh from the unfixed tree and confirm the
failing set is exactly {nested_struct, struct_by_value} on YOUR
emission before diagnosing (the reference `/tmp/emit_typed_o0` was
lifted by a plugin built from a marginally different tree).

Units/referee any time (parallel-safe): `dune runtest` (includes the
clpequiv differential referee; must stay ALL PASSED / 0 mismatches).
`dune build --profile vsa-debug` must also build. Battery dirs go on
home disk, not /tmp (it is 74% full).

## Acceptance

- `run_semantic_opt.sh` (strict, -O0 corpus) = **33 PASS / 0 FAIL**.
- `run_semantic.sh` (strict, -O0) stays **33 PASS / 0 FAIL**;
  `check_allocas.sh` stays green; `dune runtest` stays green.
- The fix is one general rule (no per-shape conditionals); grep your
  own diff for any new tag-kind/shape branch that says "cannot happen".
- -O2 corpus emission rc=0 and the pinned -O2 gate set unchanged
  (`scripts/semantic/o2_known_failures.txt`) — report any movement.
- Verdict file next to this ticket: mechanism, the fix, gate table,
  the convergence report row for nested_struct/struct_by_value
  (`scripts/semantic/convergence_report.sh <c0> <c2> <lift0> <lift2>
  <workdir>` — usage in its header).

Worktree: `/home/tovpr/hike-t1`, branch `tm/t1-opt-safety`.
