# Pins: CLP/word differential referee

Module `test/unit/test_clp_equiv.ml`. One pin in the module, `CLEQ-01`.

This module is the gate's **referee stage** (`gate.sh referee`), not part of
the per-change `dune runtest` tier: it is a domain oracle (its subject is
the vendored lattice, not a pass), and it sweeps 1.7M operand pairs.

The pin runs the full referee sweep: every `Cbat_word` export against
`Word`/`Ref_word`, the CLP identity/directional elements against the
inlined reference implementations, and the CLP pointwise operations
against the **concrete FinSet oracle** — every enumerated pair's result
must be in the CLP answer (finite operands with ≤ 64 elements; larger
or infinite ones are counted as skipped, never as checks). The
reference implementations are inlined in the pin's own source,
independent of production. The pin asserts
`checked > 1000000 && mismatches = 0`.

Production `Cbat_word.gcd_exn` is not exported; the `gcd_exn` row
cross-checks the inlined oracle against BAP, and the production path is
exercised through `lcm_exn`'s Small arm.

The pinned mechanism is the differential against the inlined references
and the concrete oracle, which are test-local, so the disable recipe is
a textual perturbation of one side.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| CLEQ-01 | the CLP/word differential referee: every op agrees with the inlined reference / concrete oracle (1,753,832 checks, 0 mismatches, 1300 both-raised, 391,344 skipped) | in `test/unit/test_clp_equiv.ml`, perturb one inlined reference (`let ref_top (i : int) = ref_bottom i`) or one production op it is compared against | demonstrated: with `ref_top = ref_bottom`, the sweep reports `checked=1753832 mismatches=2888 both-raised=1300 skipped=391344` and CLEQ-01 FAILs; restored, it passes |
