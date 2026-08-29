# Relevance two-tag contract and BAP-API cleanup

`hike_vsa_relevance.ml:20-203` mixed three concerns in one `analyze` (forward SP reach, backward slice, VLA detection), seeded reachability via ad-hoc `Core.Map` plumbing, and leaked hardcoded register strings (`"RSP"`/`"RBP"`, `is_arg_setup` over `RDI…R9`) plus scattered `is_stack_access`/`is_sp` checks across `hike_vsa.ml`, `bil2llvm.ml`, and `hike_stack_to_locals.ml`. We decided on a clean break: rename `direct_sp` (uuid `16822ae7…`) to `stack_access` with a new uuid and no alias, keep `relevant` (uuid `58a2…`) as the exact backward closure of `stack_access` over defs and phis only, decouple `dynamic_alloc` and call-arg setup from `relevant`, seed the forward fixpoint from `Targetutils.sp` alone (SP-only, `RBP` is a GPR), and rewrite traversals with `Term.visitor`/`Term.mapper`/`Exp.mapper` while keeping `Exp.free_vars` for sets. The single source for `is_sp`/`has_stack_access` lives in `Hike_vsa_relevance` and consumers delete their `String.equal "RSP"` reimplementations.

## Considered Options

- **Keep `direct_sp` uuid with alias** — rejected: leaves two names for one concept and preserves the old scattered consumers; clean break invalidates `baselines/` intentionally for the agent-returning-reader.
- **Keep `is_arg_setup` / `dynamic_alloc` inside `relevant`** — rejected: per `CONTEXT.md`, Relevance is only contributors to a Stack Access address; VLA and SysV arg writes are orthogonal and only become relevant if they flow into that address.
- **Split into separate files** — rejected: one file with four pure helpers (`collect_def_maps`, `forward_vars`, `backward_slice`, `detect_dynamic_alloc`) plus `.mli` is enough for the returning-expert reader (`Q12=a`).

## Consequences

- New `stack_access` uuid breaks old IR; corpus must be re-emitted and gates re-run (`dune runtest`, `run_corpus.sh:31/31`, `check_allocas.sh:124/0`, `semantic/run_semantic_all.sh:31/31`).
- All string-literal `RSP`/`RBP` checks and local `addr_is_stack` clones in `bil2llvm.ml:739`/`hike_vsa.ml:109`/`hike_stack_to_locals.ml:215` are removed; future SP changes go through `Targetutils.sp` only.
- Forward seed asserts `sp != fp` and strips `Var.base` normalization into one helper, making the SP-only invariant testable on BIL fixtures.
