# Pins — test_vsa (module `vsa`, prefix `VSA`)

One row per pin. Completeness: the id column equals
`dune exec test/unit/test_vsa.exe -- list`.
Production `src/` is never touched; recipes are the textual change that
disables the mechanism, re-demonstrated by review when it changes.
The Call_effects transfer pins (C1-1..C1-5) live in `test_call_effects`.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| VSA-01 | `Cbat_backward.constrain_edge` (`src/cbat_vsa/cbat_backward.ml:831`) — the `LT` guard assumps `x < 5` to `[0,4]` | make the `LT` row answer `env` unchanged (top) | VSA-01 red: `max_elem ≠ 4` / `min_elem = None` |
| VSA-02 | `constrain_edge` — the `LE` guard assumps `x <= 5` to `[0,5]` | make the `LE` row answer `env` unchanged (top) | VSA-02 red: `max_elem ≠ 5` |
| VSA-03 | `constrain_edge` — the `EQ` guard assumps `x == 5` to `{5}` | make the `EQ` row answer `env` unchanged (top) | VSA-03 red: min/max are not both `5` |
| VSA-04 | `constrain_edge` — a constant condition is doubt, the state stays top | make the constant arm refine `x` to the constant | VSA-04 red: `is_top` fails |
| VSA-05 | `constrain_edge` — a width-mismatched guard is doubt, the state stays top | make the width-mismatch arm coerce and refine | VSA-05 red: `is_top` fails |
| VSA-06 | `constrain_edge` — the gate-free `NEQ` row answers `TOP−{5}` | make the `NEQ` row answer `env` unchanged | VSA-06 red: `is_top` or `5 ∈` the set |
| VSA-07 | `constrain_edge` — a bare flag guard forces the flag to `{1}` | make the bare-var arm answer `env` unchanged | VSA-07 red: the flag is not `{1}` |
| VSA-08 | `constrain_edge` — a `NOT` flag guard forces the flag to `{0}` | make the `NOT` arm answer `env` unchanged | VSA-08 red: the flag is not `{0}` |
| VSA-09 | `Cbat_vsa.static_graph_vsa` (`cbat_vsa.ml:151`) + `Cbat_forward.denote_block` — the trace partition: the back-edge target's IN-state is the guard-refined iterate view | drop the taken-edge refinement so the body IN-state is the header's unrefined state | VSA-09 red: `max_elem c_iter > 4` / `is_top c_iter` |
| VSA-10 | `Cbat_clp.equal` mixed-width coercion (`src/cbat_vsa/cbat_clp.ml`) | textually invert the pinned contract: make `equal` compare across widths | VSA-10 red: the mismatched pair compares true |
| VSA-11 | `Cbat_clp.subset` mixed-width coercion | make `subset` compare across widths | VSA-11 red: the mismatched pair is a subset |
| VSA-12 | `Cbat_clp.intersection` mixed-width coercion → wider operand | make `intersection` raise or return bottom on mismatch | VSA-12 red: `bitwidth ≠ 64` / not `equal r p64` |
| VSA-13 | `Cbat_clp.add` mixed-width coercion | make `add` raise on mismatch | VSA-13 red: raise or missing `{2,3,4}` elements |
| VSA-14 | `Cbat_clp.mul` mixed-width coercion | make `mul` raise on mismatch | VSA-14 red: raise or missing `{1,4}` elements |
| VSA-15 | `Cbat_clp.logand` mixed-width coercion | make `logand` raise or return bottom | VSA-15 red: raise / `is_bottom` |
| VSA-16 | `Cbat_clp.logxor` mixed-width coercion | make `logxor` raise or return bottom | VSA-16 red: raise / `is_bottom` |
| VSA-17 | `Cbat_clp.div` mixed-width coercion | make `div` raise or return bottom | VSA-17 red: raise / `is_bottom` |
| VSA-18 | `Cbat_clp.sdiv` mixed-width coercion | make `sdiv` raise or return bottom | VSA-18 red: raise / `is_bottom` |
| VSA-19 | `Cbat_clp.join` mixed-width coercion | make `join` raise on mismatch | VSA-19 red: raise / missing `{1,2}` elements |
| VSA-20 | `Cbat_clp.widen_join` mixed-width coercion | make `widen_join` raise on mismatch | VSA-20 red: raise / missing `{1}` |
| VSA-21 | `Cbat_clp.meet` mixed-width alias → wider operand | make `meet` raise or return bottom on mismatch | VSA-21 red: `bitwidth ≠ 64` / not `equal r p64` |
| VSA-22 | `Cbat_clp.add` same-width regression | make the same-width arm coerce the result width | VSA-22 red: `bitwidth ≠ 32` / missing `{11,13}` |
| VSA-23 | `Cbat_transfer.denote_def` (`cbat_transfer.ml:325`) — the mixed-width `RSHIFT` COMPUTES (no `not_implemented` fire) | route mixed-width shifts through `not_implemented ~top` | VSA-23 red: `fired_r` true or `j_after` is top |
| VSA-24 | `Cbat_fin_set.union` lift2 default width | make `union` assert or keep the narrower width | VSA-24 red: raise / `bitwidth ≠ 64` |
| VSA-25 | `Cbat_fin_set.intersection` lift2 default width | make `intersection` assert or keep the narrower width | VSA-25 red: raise / `bitwidth ≠ 64` |
| VSA-26 | `Cbat_fin_set.add` lift2 default width | make `add` assert or keep the narrower width | VSA-26 red: raise / `bitwidth ≠ 64` |
| VSA-27 | `Cbat_fin_set` same-width union/intersection regression | make the same-width arm widen the result | VSA-27 red: the exact union/intersection fails |
| VSA-28 | `Cbat_vsa_utils.not_implemented` (`cbat_vsa_utils.ml:21`) — logs through `Event.Log` only, no stderr line | replace the log arm with `Format.eprintf` of the component | VSA-28 red: `probe_lines` non-empty |
| VSA-29 | `not_implemented` — no marker leaks to stderr at all | add a `prerr_endline "not_implemented (degrading to top)"` arm | VSA-29 red: the captured stderr contains the marker |
| VSA-30 | `constrain_edge` — the gate-free `EQ` guard refines `x` to `{5}` (T3 fixture) | make the `EQ` row answer `env` unchanged | VSA-30 red: min/max are not both `5` |
| VSA-31 | `constrain_edge` — same `EQ` refinement, second read (the gate-free contract) | same `EQ`-row recipe as VSA-30 | VSA-31 red: min/max are not both `5` |
| VSA-32 | `constrain_edge` + the flag def chain — the mixed-def flag IS refined to `{1}` on the taken edge | make the flag-guard arm answer `env` unchanged | VSA-32 red: `{1}` not the taken flag value |
| VSA-33 | the single-def flag control refines identically | same flag-guard recipe as VSA-32 | VSA-33 red: `{1}` not the taken flag value |
| VSA-34 | `Cbat_call_effects.transfer` (`src/cbat_vsa/cbat_call_effects.ml:31`) — the post-call reload reads TOP | keep the aliased cell live across the call (skip the escape/kill) | VSA-34 red: `find_word 64` is not top |
| VSA-35 | the call's memory effect — post-call memory is entirely TOP (no frame proof) | keep the caller frame (`call_abstraction_frame`) with an unbounded RSP | VSA-35 red: `find_memory ≠ Mem.top` |
| VSA-36 | the call's SP restore — `RSP` is preserved across the call | drop the `RSP`-preserved arm from the preserved set | VSA-36 red: `RSP ≠ {0x2000}` |
| VSA-37 | the call's frame-keep — `RBP` is preserved across the call | treat `RBP` as caller-saved | VSA-37 red: `RBP ≠ {0x100}` |
| VSA-38 | the call's frame-keep — callee-saved `RBX` is preserved | treat `RBX` as caller-saved | VSA-38 red: `RBX ≠ {0x2040}` |
| VSA-39 | the call's escape — caller-saved `rdi` is TOPed | keep `rdi` in the preserved set | VSA-39 red: `rdi` is not top |
| VSA-40 | `Cbat_map_lattice.Make_val(...).fold` (`cbat_map_lattice.ml:154`) — visits the explicit bindings | make `fold` skip the explicit bindings | VSA-40 red: `seen ≠ [(1,10);(2,20)]` |
| VSA-41 | `fold` — an absent key (top) is not visited | make `fold` visit absent keys | VSA-41 red: `fold Map.top` is non-empty |
| VSA-42 | `Cbat_clp.cast` (`cbat_clp_arith`, re-exported `cbat_clp.ml:34`) — `HIGH` size 0 → top(64) | make the degenerate-size arm compute a singleton | VSA-42 red: `is_top` fails |
| VSA-43 | `Clp.cast` — `HIGH` size > width → top(64) | make the over-wide arm compute a singleton | VSA-43 red: `is_top` fails |
| VSA-44 | `Clp.cast` — `UNSIGNED` size 0 → top(32) | make the degenerate-size arm compute a singleton | VSA-44 red: `is_top` fails |
| VSA-45 | `Clp.cast` — `SIGNED` size 0 → top(32) | make the degenerate-size arm compute a singleton | VSA-45 red: `is_top` fails |
| VSA-46 | `Clp.cast` — `LOW` size 0 → top(32) | make the degenerate-size arm compute a singleton | VSA-46 red: `is_top` fails |
| VSA-47 | `Clp.extract` — `~lo:width` → top (no assert) | make the out-of-range `lo` arm assert | VSA-47 red: raise or non-top |
| VSA-48 | `Clp.extract` — `~hi:(-1)` → top (no raise) | make the negative `hi` arm compute a masked result | VSA-48 red: raise or non-top |
| VSA-49 | `Cbat_clp_set_composite.cast` (`cbat_clp_set_composite.ml:684`) — `HIGH` size 0 → top(64) | make the composite cast arm return the FinSet-backed stub | VSA-49 red: `is_top` fails |
| VSA-50 | `Cbat_clp_set_composite.extract` (`:666`) — `hi < lo` → top(32) | make the inverted-range arm assert or compute | VSA-50 red: raise or non-top |
| VSA-51 | `Cbat_clp_set_composite.extract` — `hi < 0` (lo defaults 0) → top(32) | make the negative-`hi` arm compute | VSA-51 red: raise or non-top |
| VSA-52 | `Cbat_transfer.denote_def` — `RAX := high:0[RAX]` after a call denotes and the fixpoint completes, `RAX = top(64)` | make the zero-size `HIGH` cast raise in `denote_def` | VSA-52 red: the fixpoint raises / `RAX ≠ top` |
| VSA-53 | `Cbat_clp.equal` physical-identity short-circuit | make `equal` compare canonical payloads only | VSA-53 red: `equal p p` false |
| VSA-54 | `Cbat_clp.equal` structural equality of separate builds | make `equal` compare physical identity only | VSA-54 red: `equal p q` false (the canonical form differs) |
| VSA-55 | `Cbat_clp.equal` unequal values still false | make `equal` answer true when the canonical forms share elements | VSA-55 red: `equal p r` true |
| VSA-56 | `Cbat_clp.equal` width-mismatched values false, no raise | make `equal` raise on width mismatch | VSA-56 red: raise or true |
| VSA-57 | `static_graph_vsa` / `Cbat_forward.denote_block` — the counter-shift loop's trace partition (iterate ⊆ [0,4], exit min ≥ 5) | drop the taken-edge refinement so the body IN-state is unrefined | VSA-57 red: `max_elem c_iter > 4` / `min_elem c_exit < 5` |
| VSA-58 | the counter window survives the body shift (`y = x << (i+1)`) | make the shifted def flow back unrefined into the header | VSA-58 red: `is_top c_iter` or `max_elem > 4` |
| VSA-59 | `Cbat_transfer.denote_def` store cell (`cbat_transfer.ml:268`) — the heap-indexed store's data var is denoted `{99}` | make the store arm leave the environment unchanged | VSA-59 red: `vv ≠ {99}` |
| VSA-60 | `Cbat_vsa.init_sol` (`cbat_vsa.ml:49`) — the entry `RSP` anchor is the symbolic segment base at offset 0 (`StackOff{0}`) | seed the entry `RSP` with `Ws.top 64` instead of `stack_word_i64 0` | VSA-60 red: `find_word 64` ≠ `stack_word_i64 0` |
| VSA-61 | `Cbat_clp_set_composite.cardinality` (`:257`) + `Cbat_fin_set.cardinality` (`:35`) — the full 1-bit domain reads cardn 2 (width+1 bits) | read the cardinality at the set width (1 bit) | VSA-61 red: cardn wraps to 0 / ≠ 2 |
