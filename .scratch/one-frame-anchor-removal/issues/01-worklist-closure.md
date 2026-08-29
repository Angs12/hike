# 01: Worklist closure in backward-slice `block_contributors` (DONE)

**What to build:** `block_contributors` computes the transitive closure
of `relevant` defs starting from the per-block `stack_access` seeds.
The current implementation is a `while changed` loop with `ref`-mutated
sets, redundant per-round `base_var` recomputation, and an inner fixpoint
inside the outer `backward_slice` fixpoint (worst-case O(n²) per block
× O(2^n) outer rounds). The fix replaces it with a pure tail-recursive
worklist: each non-seed def is enqueued at most once, its LHS is hoisted
out of the inner computation, and the producer of each newly-introduced
var is looked up via `def_of_lhs` to extend the worklist. No `ref`, no
`while`, all data flow is threaded through the `loop` function.

**Blocked by:** None (can start immediately). Independent of every other
ticket in this workstream.

**Status:** done (in the worktree, uncommitted). Ready for review +
commit.

- [ ] `block_contributors` is a pure function (no `ref`, no `while`).
- [ ] `base_var (Def.lhs d)` is hoisted out of the inner loop into a
  pre-built list of `(lhs, def)` pairs.
- [ ] The worklist is extended via `def_of_lhs` lookups for each newly-
  introduced var in a def's RHS.
- [ ] `dune runtest` green: all 12 T4 checks pass; the 3 LM F1/F2c
  failures remain (pre-existing).
- [ ] `dune build @install && dune install && cd src && bapbuild
  -clean && make` succeeds.
- [ ] `bash scripts/run_corpus.sh /tmp/corpus /tmp/heritage_worklist`
  → 31/31 rc=0, 24 surviving `hike: guarded:` warnings (Unbounded,
  va_arg alignment-split).
- [ ] `bash scripts/check_allocas.sh /tmp/heritage_worklist` → 124/0.
- [ ] `bash scripts/semantic/run_semantic.sh /tmp/corpus
  /tmp/heritage_worklist /tmp/sem_worklist` → 8/8.
- [ ] `bash scripts/semantic/run_semantic_all.sh /tmp/corpus
  /tmp/heritage_worklist /tmp/sem_all_worklist` → 28/31 (3 failures:
  nested_struct, va_arg_vacopy, variadic — pre-existing in uncommitted
  work, NOT caused by this fix).
- [ ] `AGENTS.md` §Current validation state updated with the new
  timestamp and the worklist-closure ticket number.
