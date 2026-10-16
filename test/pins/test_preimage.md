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
