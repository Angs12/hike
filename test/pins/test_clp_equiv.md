# Pins: CLP/word differential referee

Module `test/unit/test_clp_equiv.ml`. One pin in the module.

The pin runs the full referee sweep: every `Cbat_word` export against
`Word`/`Ref_word`, and the CLP identity/op/directional sweep against the
inlined reference implementations, over the sampled widths (1..64 plus
64/65/129). The reference implementations are inlined in the pin's own
source, independent of production. The pin asserts
`checked > 1000000 && mismatches = 0`; the old probe's `exit 1` is that
assertion.

The pinned mechanism is the differential against the inlined references,
which are test-local, so the disable recipe is a textual perturbation of
one side.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| CLEQ-01 | the CLP/word differential referee: every op agrees with the inlined reference (2,861,148 checks, 0 mismatches, 1300 both-raised) | in `test/unit/test_clp_equiv.ml`, perturb one inlined reference (`let ref_top (i : int) = ref_bottom i`) or one production op it is compared against | demonstrated: with `ref_top = ref_bottom`, the sweep reports `checked=2861148 mismatches=2888 both-raised=1300` and CLEQ-01 FAILs (Expected `true`, Received `false`); restored, it passes |
