# Pins: CLP/word differential referee

Module `test/unit/test_clp_equiv.ml`. One pin in the module, `CLEQ-01`.

This module is the gate's **referee stage** (`gate.sh referee`), not part of
the per-change `dune runtest` tier: it is a domain oracle (its subject is
the vendored lattice, not a pass), and it sweeps ~1.93M operand pairs.

The pin runs the full referee sweep: every `Cbat_word` export against
`Word`/`Ref_word`, the CLP identity/directional elements against the
inlined reference implementations, and the CLP pointwise operations
against the **concrete finite-set oracle** — every enumerated pair's result
must be in the CLP answer (finite operands with ≤ 64 elements; larger
or infinite ones are counted as skipped, never as checks). A
**composite-layer** sweep drives `Cbat_clp_set_composite`'s own binops
(`Ws.sub`/`div`/`sdiv`/`modulo`/`smodulo`/`lshift`/`rshift`/`arshift`/
`concat`) and unary `Ws.extract` over a mixed pair — a small exact
`Exact` value against a `Clp`-represented progression (count > `fin_set_size`,
so canonicalization keeps it a Clp), in both operand orders — so a
non-commutative op in `op_pair`'s mixed arm cannot swap its operands.
The operand set includes zero: an exact-zero divisor's image is the
concrete elementwise one (`ones` for a non-negative dividend, `1` for a
negative one, their union when both occur). The reference implementations
are inlined in the pin's own source, independent of production. The pin
asserts `checked > 1000000 && mismatches = 0`.

Production `Cbat_word.gcd_exn` is not exported; the `gcd_exn` row
cross-checks the inlined oracle against BAP, and the production path is
exercised through `lcm_exn`'s Small arm.

The pinned mechanism is the differential against the inlined references
and the concrete oracle, which are test-local, so the disable recipe is
a textual perturbation of one side.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| CLEQ-01 | the CLP/word differential referee: every op agrees with the inlined reference / concrete oracle, and the composite's mixed `Exact`/`Clp` binops keep each operand on its own side (1,934,763 checks, 0 mismatches, 1300 both-raised, 405,288 skipped) | in `test/unit/test_clp_equiv.ml`, perturb one inlined reference (`let ref_top (i : int) = ref_bottom i`), or revert the mixed-arm operand order (the reverse of commit `454ce52`, in the current identifiers: `| Ps ps, Fs s \| Fs s, Ps ps -> [ Clp (binop_pieces op ps (pieces_of_exact s)) ]`), or restore `sdiv_core`'s exact-zero arm to `singleton (W.ones width)` | demonstrated: with `ref_top = ref_bottom`, the sweep reports `checked=1934762 mismatches=2888 both-raised=1300 skipped=405288` and CLEQ-01 FAILs. With the mixed arm's order reverted, it reports `checked=1934762 mismatches=224` — every printed one in the `EX,CLP` order (e.g. `COMP sub EX,CLP w=8 b1=0 b2=0 s2=1 c2=12: 0:8u 0xB:8u -> 0xF5:8u is outside the result`) — and CLEQ-01 FAILs. With the pre-fix exact-zero arm, it reports `checked=1934762 mismatches=2`, both `COMP sdiv CLP,EX` (a negative dividend's `1` outside `{ones}`), and CLEQ-01 FAILs; fixed, it passes |
