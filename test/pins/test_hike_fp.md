# Pins — test_hike_fp

Module: `test/unit/test_hike_fp.ml` (group `hike_fp`, ids `HFP-01`…).
Production mechanism: `src/hike_fp.ml`, called by
`Hike_program_vsa.normalize` after width coercion and before each VSA solve. The x86 lifter uses one intrinsic
temp name (`intrinsic:x0`) at several widths — single- and
double-precision share the unsized `_binary` intrinsic spelling — and
BAP's var identity is `(name, version)`, type-blind, so a
model-declared width and the lifter's collide: a phi mints at the
model's width while its incomings carry the instruction's, and a concat
over the temp stops summing to its width.  The pass qualifies every
`intrinsic:xN`/`intrinsic:yN` occurrence (any arity) by its own width
and rewrites each mapped FP call's target to the table's sized spelling
for its operand width — the nearest preceding temp def in term order —
so no later pass resolves a width.

The emitter-side pins (the table's rows and their emission) are
FP-01…FP-29 in `test_emit_fp.md`; its fixture runs this pass, so those
pins see the qualified names.

Every pin builds its own subs inside its closure; no emitter runs here.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| HFP-01 | the pass qualifies a temp def's lhs and every read of it by the width the lifter wrote (`intrinsic:x0` at 64 bits becomes `intrinsic:x0:64`). | In `qualify`, return `v` unchanged. | HFP-01 FAILs: the name carries no width. |
| HFP-02 | the same source name at two widths stays two identities: a 32-bit def and a 64-bit def of `intrinsic:x0` become `intrinsic:x0:32` and `intrinsic:x0:64`. | Make `qualify` use a fixed width. | HFP-02 FAILs: both defs collapse to one name. |
| HFP-03 | a mapped FP call whose target carries no width is rewritten to the table's sized spelling for the nearest preceding temp def's width. | Drop the `sized_name` rewrite in `tag_targets`. | HFP-03 FAILs: the target keeps the untagged spelling. |
| HFP-04 | an already-sized target and a non-mapped target are untouched by the width qualification (the table's rows are sound) | size every target unconditionally | pin FAILs: the unmapped target is rewritten |
| HFP-05 | an unqualified mapped target whose temp width has no sized row (only 32/64 have them — the 80-bit class) stays unqualified AND warns through `Hike_diag` (`hike_fp.tag_targets`), so the residue is loud and every consumer's `lane_width_of_name` word-width fallback is the recorded answer | delete the `Hike_diag.warn` in `tag_targets`' `sized_name` miss | HFP-05 red: the warn line is absent |
