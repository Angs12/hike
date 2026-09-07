# fixture-lib — consolidate the BIR fixture builders into test_common.ml

Branch: `fixture-lib` (stacked on `honest-gate` @ 48efc70).
Grilling-settled 2026-09-07 (8 questions, Q1–Q9).

## The problem (measured)

967 `Blk.Builder` calls across 6 test files, zero in `test_common.ml`:
backward 441 (15 private `mk_*` loop builders), vsa 172 (5 builders),
regression 143, properties 128, bil2llvm 43, dce 40. Each file
hand-rolls its own builders; near-duplicate locals (`mk_store` in dce
+ regression, exit-block idioms) are built twice. Writing a new
edge-case test means re-deriving BIR plumbing before the edge case.

## The decisions (grilling-settled)

1. Move ALL builders into `test_common.ml` — including single-consumer
   ones. This is relocation into the existing shared file, NOT a new
   seam: no new module, no `.mli`, no interface claims.
2. Builders produce BIR subs/blocks/defs and `vsa_info` VALUES only —
   never call `Kb.provide`. The global KB write stays visible at each
   test site (a fixture that silently provides would hide a global
   side effect behind a local-looking call, and double-provide of a
   tid raises `Vsa_info_conflict`).
3. Both `mk_store` variants move verbatim under distinct names — no
   unification, no call-site churn beyond the module prefix.
4. Incremental, green each step: one file per commit in stanza order
   (domains → seed → vsa → backward → regression → properties → dce →
   bil2llvm). Bar per step: direct-exe runtest green at the 494
   baseline. No corpus battery: test files never link into the plugin,
   so pure test-file moves cannot change production behavior.
5. Signatures are unchanged by the move — call sites gain only the
   removal of `local` shadowing (builders become top-level in
   test_common.ml; name collisions resolved by keeping the existing
   names, which are already file-unique — verified: test_common.ml
   defines no `mk_*` today).

## The bar

- After every ticket: `dune exec test_cbat/test_main.exe` → 494 ok,
  0 FAIL (direct-exe count; dune's captured output truncates).
- Final: full `dune runtest` green (incl. the clpequiv referee from
  candidate #3), `dune build @all` clean, and a name-collision audit
  (`grep -n "^let mk_" test_cbat/test_common.ml` vs per-file locals).
- Net code movement only: total check count MUST stay 494 throughout
  (no check added, none removed, none renamed).
