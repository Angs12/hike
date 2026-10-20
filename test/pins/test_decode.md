# Pins — test_decode

Module `src/hike_decode.ml` (`Hike.Decode`), the per-function body over
BAP's decoded state. One row per pin in `test/unit/test_decode.ml`. The
fixtures are `Harness.with_binary` ELFs (code at 0x400078).

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| DEC-01 | `function_cfg` explores from the entry with `follow` false at other entries, so a callee's blocks stay out; `is_call`, `dests` and `dest` name the call block's decoded destination | make `follow` always true | DEC-01.blocks FAILs: the callee block 0x40007e joins (review) |
| DEC-02 | `trim` drops a call block's fallthrough when `keep_fall` rejects it and keeps only what the entry reaches; `lift` gives the call no return and names the sub | keep every edge in `trim` | DEC-02.noreturn.* FAIL (review) |
| DEC-03 | a jump into another entry is not followed, so the target stays out of the body | as DEC-01 | DEC-03 FAILs (review) |
| DEC-04 | `lift` carries BAP's operation-specific atomic intrinsic for a locked RMW and no generic lock markers | pair the decode with the generic lock producer | review |
