# Pins: precision-probe classification

Module `Precision_probe_rows` (`test/probe/precision_probe_rows.ml`). One row
per pin in `test/unit/test_probe.ml`.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| PROBE-01 | `classify_shape` reads the value's runtime origin: a symbolic stack value is `Stack`, a plain value whose absolute extrema land in the segment is `Lost`, and each origin arm maps (`Window`, `Vla`, `Rip`→`Other`) | make `classify_shape` answer `Lost` unconditionally | pin FAILs: the symbolic arm reads `Lost` |
| PROBE-02 | the five stack-flagged access shape counters sum to the `ldstk` population: `add_ld` counts a shape exactly when `stack` | drop the `if stack then add_ld_shape s shape` guard | pin FAILs: the shape sum reads 6 against a population of 5 |
| PROBE-03 | the five stack-flagged def shape counters sum to the stack-flagged def population: `add_def` counts a shape exactly when `stack` | drop the `if stack then add_def_shape s shape` guard | pin FAILs: the shape sum reads 6 |
