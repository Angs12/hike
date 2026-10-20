# Pins: precision-probe classification

Module `Precision_probe_rows` (`test/probe/research/precision_probe_rows.ml`). One row
per pin in `test/unit/test_probe.ml`.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| PROBE-01 | `classify_shape` reads the value's runtime origin: a symbolic stack value is `Stack`, a caller-frame stack value (all offsets at/above the ABI word) is `Window`, a plain value whose absolute extrema land in the segment is `Lost`, and a `Rip` origin maps to `Other` | make `classify_shape` answer `Lost` unconditionally | pin FAILs: the symbolic arm reads `Lost` |
| PROBE-02 | the four access shape counters sum to the non-bottom `ldstk` population: `add_ld` counts a shape exactly when `stack` and the shape is `Some` (both bottom buckets sit in the population, `shape:None`) | drop the `if stack then Option.iter (add_ld_shape s) shape` guard | pin FAILs: the shape sum reads 6 against a non-bottom population of 5 |
| PROBE-03 | the four def shape counters sum to the shape-carrying stack-flagged def population: `add_def` counts a shape exactly when `stack` and the shape is `Some` | drop the `if stack then Option.iter (add_def_shape s) shape` guard | pin FAILs: the shape sum reads 7 |
| PROBE-04 | `is_stack_value` accepts stack-family origins and diagnostic bottom only: a magic, a band-reaching integer, a sign-crossing hull and a frame-band literal all read non-stack; `shape_of` omits bottom | restore numeric-band inference | a plain value incorrectly reads stack |
