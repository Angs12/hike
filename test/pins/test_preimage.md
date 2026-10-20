# Pure backward operator pins

The owning seams are `Cbat_clp.Exact.backward1/backward2`,
`Cbat_clp.Pieces.backward1/backward2`, and the word-set dispatch. The shared
`Cbat_preimage.Make` functor assembles alternative input projections.

| Pin | Contract | Falsification |
|---|---|---|
| INV-01 | A LOW inverse over the separated byte-minus-nine ranges narrows to 24 inputs, both at Pieces and through the real backward walk. | Take global bounds before distributing the inverse. |
| INV-02 | Exact filtering preserves disjoint unary alternatives and both projections of satisfying binary pairs. | Intersect alternatives or retain a pair whose image misses the result. |
| INV-03 | Binary lifting distributes both operand and result pieces without filling the gap. | Hull either set before inversion. |
| INV-04 | Every concrete binary pair satisfying the result survives both Pieces projections, checked against BAP semantics across arithmetic, shifts, bitwise operators and comparisons. | Exclude a satisfying input, including a wrapped shift or negative quotient. |
| INV-05 | Every concrete satisfying cast, extract, NOT and NEG input survives its Pieces pre-image. | Lose a sign-extended or repeated bit window. |
| INV-06 | Mixed finite/piece arithmetic keeps a stack origin; an impossible inverse retains the input width. | Materialize the stack origin or let an empty Pieces width change the operand width. |
| INV-07 | An inverse that rejects the current value still supplies the excluding boundary to landmark acquisition. | Propagate only an empty projection and lose the boundary. |
| INV-08 | A disabled flag carries its requested polarity through the observer without entering live analysis state. | Seed the flag with its current, opposite polarity. |
| INV-09 | A periodic LOW constraint retains its stride across more than 64 windows, including at width 64. | Hull a complete repeating residue class instead of retaining its progression. |
| INV-10 | A constant is admitted unless a result of its own width excludes it: in-range admitted, disjoint rejected, bottom rejected, width-mismatched admitted; `constrain_operands` makes the env bottom on an excluded constant. | Reject a constant whenever the result width differs, or admit a disjoint result. | INV-10.in/out/width/walk FAIL under that inversion. |
| INV-11 | Binary kernels keep every satisfying pair for wrapped results and signed divisors across arithmetic, shifts, bitwise operators, and comparisons. | Exclude a satisfying input, such as a wrapped shift or a negative quotient. | INV-11 FAILs: a satisfying pair is missing. |
| INV-12 | Unary kernels keep every satisfying input for wrapped results and a full-width extract across NOT, NEG, casts, and extracts. | Lose a sign-extended or repeated bit window. | INV-12 FAILs: a satisfying input is missing. |
| INV-13 | Stack-relative inverses keep every satisfying value for each concrete base, with offsets taken relative to the aligned base. | Use absolute addresses instead of relative offsets. | INV-13 FAILs: a satisfying stack value is missing. |
