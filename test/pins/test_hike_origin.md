# Pins: Hike_origin

Module `hike_origin` (`src/hike_origin/hike_origin.ml`).
One row per pin in `test/unit/test_hike_origin.ml`.

The module is the origin leaf library: the ADT and its per-origin facts
table.  Red evidence is by review: each disable recipe is the textual
inversion of the pinned branch, and the pin's exact-equality assertion
fails under that inversion.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| ORI-01 | `facts Stack`: base = `segment_base` (2^62+8), certified 4, ±8 MiB clamps | change `facts Stack`'s `base` to `0L` | pin FAILs: the base assert fails |
| ORI-02 | every origin has a name; the listing match is exhaustive, so a new constructor stops compiling until it is listed | drop a constructor from the `name` match | pin FAILs: the name assert fails (inexhaustible match) |
| ORI-03 | `origin`: a stack value reads `Some Stack`; a plain singleton, an absolute Clp, and a stack∪plain union read `None` | make `origin` answer `Some Abs` for `Clp _` | pin FAILs: the plain/absolute asserts fail |
| ORI-07 | the store→load round-trip (frame): the load's stamped ADDRESS origin (a frame cell) is `Some Stack` | make `stamp_origin` use the loaded value for a load instead of the address | pin FAILs: the read-back origin is `Some Abs`/the value's |
| ORI-18 | the D10 namespace test (`names_stack_line`): `Stack` names the stack line; `Abs` and `Rip _` name none | make `names_stack_line` answer `true` for `Abs` | pin FAILs: the absolute-origin assert fails |

| ORI-19 | equality distinguishes every origin and section; arithmetic, enumeration and memory keys follow the source origin; a `Rip` module address is exact on the absolute line, keeps its section through displacement and masking, and a union keeps each section beside the plain words (ADR 0035) | ignore origins in equality, or give Rip an unknown base | distinct origins compare equal, or Rip values stop enumerating |

| ORI-20 | Abs arithmetic and materialization preserve exact absolute bits, including high-bit words | send Abs through symbolic-base arithmetic | multiplication/negation return TOP or materialization loses bits |
| ORI-22 | full-width memory preserves every origin's payload; Rip shares the absolute line | drop payload origin or separate the Rip/Abs namespaces | payload or pairwise key checks fail |
| ORI-23 | alignment images count rounded blocks rather than the original span | count blocks from the unrounded endpoints | a boundary-crossing interval loses its second result |

| ORI-24 | relative difference uses exact shared offsets; a module-address subtrahend removes exactly its link-time words | subtract materialized relative hulls | disjoint Rip offsets or a plain value incorrectly become bottom |
| ORI-26 | certified-bit OR/XOR of a stack value stays on the stack line: `stack[0] \| 7 = stack[7]`, `stack[0] ^ 8 = stack[-8]`; a constant with bits above the certified count (`0x100`) answers top | route `Logor`/`Logxor` back to the hard top for a relative in `lift2`/`rel_table` | pin FAILs (OR/XOR of a stack value is top, or drops the origin) |

| ORI-27 | T35: a set-valued SP (two guarded sizes) followed by a fixed page decrement stays on the `Stack` origin with the exact shifted positions; SP arithmetic is ordinary Stack arithmetic. | reintroduce an allocation event that rebases the SP | ORI-27 red: the origin is no longer `Stack` or the positions widen. |
| ORI-28 | FS self-pointer load, subtraction, stack spill/reload and final address retain their origins. | omit the FS entry seed or self-pointer read rule | fails on the pre-repair sources at the first FS load |
| ORI-29 | FS bases remain symbolic through bounds, constraints, difference, mixed widening and comparison; shared-base subtraction uses offsets. | materialize FS using a fixed zero base | a plain constraint removes a reachable FS value or exposes invented bounds |
| ORI-30 | Foreign calls preserve the ABI thread pointer. | omit the thread pointer from `preserved_of_sub` | the post-call self-pointer load loses FS origin |
| ORI-31 | An explicit memory write to the TCB self cell overrides its ABI default. | return FS[0] without checking stored cells | the load returns a pointer instead of the stored 42 |
