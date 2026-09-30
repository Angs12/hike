# Pins: precision-probe classification

Module `Precision_probe_rows` (`test/probe/precision_probe_rows.ml`). One row
per pin in `test/unit/test_probe.ml`.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| PROBE-01 | `classify_shape` reads the value's runtime origin: a symbolic stack value is `Stack`, a plain value whose absolute extrema land in the segment is `Lost`, and each origin arm maps (`Window`, `Vla`, `Rip`→`Other`) | make `classify_shape` answer `Lost` unconditionally | pin FAILs: the symbolic arm reads `Lost` |
| PROBE-02 | the five access shape counters sum to the non-bottom `ldstk` population: `add_ld` counts a shape exactly when `stack` and the shape is `Some` (both bottom buckets sit in the population, `shape:None`) | drop the `if stack then Option.iter (add_ld_shape s) shape` guard | pin FAILs: the shape sum reads 6 against a non-bottom population of 5 |
| PROBE-03 | the five def shape counters sum to the shape-carrying stack-flagged def population: `add_def` counts a shape exactly when `stack` and the shape is `Some` | drop the `if stack then Option.iter (add_def_shape s) shape` guard | pin FAILs: the shape sum reads 7 |
| PROBE-04 | `is_stack_value`: the dead-path bottom, the symbolic arm (a value carrying a runtime origin), or a plain value whose extrema form a non-crossing interval inside the frame band around `stack_base`; `shape_of` answers `None` for the bottom | make `shape_of` answer `Some (classify_shape ws)` unconditionally | pin FAILs: the bottom reads a `Lost` shape |
| PROBE-05 | `is_stack_value` rejects a plain hull crossing the sign boundary (its int64 `max` reads negative, so `min ≤ max` fails) | drop the `Int64.compare mni mxi <= 0` guard | pin FAILs: the crossing hull reads stack |
| PROBE-06 | a plain literal inside the frame band (`0x3FFFFFFFFFFFFFFF`, `stack_base − 9`) is admitted and reads `Lost`: the composite exposes no provenance for a plain value, so a literal is indistinguishable from a demoted frame address | require `Ws.origin` (drop the plain arm) | pin FAILs: the literal reads not-stack |
