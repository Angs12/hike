# Pins: Hike_types

Module `src/hike_types.ml` (no interface; all let-bindings visible).
One row per pin in `test/unit/test_hike_types.ml` (ids `TYPES-01`..`TYPES-23`).

The module is the home of each lane's type: the program's per-sub emission
signature.  The pins drive the pure/decidable surface on hand-built BIR
subs, using the real `Hike_abi.x86_64_sysv` convention and the
`x86_64-gnu-elf` target where the ABI return lanes matter.

Two BAP encoding facts drive the fixtures (not the module):
a terminal `Ret` round-trips as a call and would fire the PLT rule, so the
lane-shape pins use `plain_sub` (one block, no jumps); and `Tid.for_name`
prefixes `"@"`, so `@main` is `Tid.for_name "main"`.

Red evidence is by review: each disable recipe is the textual inversion of
the pinned branch in `hike_types.ml`, and the pin's exact assertion fails
under that inversion.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| TYPES-05 | `tag_lane`: a plain `In` register lane is left untagged. | In `tag_lane`, drop the pointer guard (always `set_ptr_arg`). | TYPES-05 FAILs: the lane becomes a pointer. |
| TYPES-10 | `compute_sub_sig`: an unknown target answers no returns (the target check is the switch). | As TYPES-09 but make the target test always `true`. | TYPES-10 FAILs: the unknown target gains RAX/RDX. |
| TYPES-12 | `compute_sub_sig`: SP, the thread pointer, and callee-saved registers are filtered from argument lanes. | In the `filter`, drop the `is_callee_saved`/`Abi.sp`/`thread_pointer` disjuncts. | TYPES-12 FAILs: RSP/RBX/FS_BASE become args. |
| TYPES-13 | `compute_sub_sig`: intrinsic-target and promoted (`hike_slot`/`hike_arg`) names are filtered from argument lanes. | In the `filter`, drop the intrinsic-name/`hike_slot`/`hike_arg` disjuncts. | TYPES-13 FAILs: the promoted lanes become args. |
| TYPES-16 | `compute_sub_sig`: a `window_param` layout carries the caller window as a pointer `In` lane. | In `compute_sub_sig`, drop the `window_arg` append (`args @ []`). | TYPES-16 FAILs: the window lane is absent. |
| TYPES-17 | `compute_sub_sig`: an emittable intrinsic takes its free vars `In` and its own defs `Out`. | In the intrinsic branch, skip the def scan for returns (return the target's `rets`). | TYPES-17 FAILs: the intrinsic's `Out` lane is absent. |
| TYPES-18 | `compute_sub_sig`: every internal sub carries the ABI return carriers (RAX, RDX, YMM0); the boundary (the C entry) and unknown targets do not. | In `compute_sub_sig`, drop the `vector_return_reg` from the carriers (or take the `fixed_signature` branch for every sub). | TYPES-18 FAILs: YMM0 is missing (a boundary-only signature). |
| TYPES-22 | A named external call receives the synthetic parameter-register ABI even when its target sub is not in the filtered program. | In `is_native_call`, classify every generated no-return direct target as a real call. | TYPES-22 FAILs: the external-call sub has no synthetic argument lanes. |
| TYPES-23 | A canonical direct `hike_return` edge is not a native call and does not add synthetic parameter lanes. | In `is_native_call`, count the canonical direct return as a call. | TYPES-23 FAILs: the terminal-return sub has synthetic argument lanes. |
| KIND-01 | a def computing a stack address is ptr-kind (its denotation is stack-resident) — the emitter's pointer argument depends on it | drop the denotation seed from `ptr_defs` | pin FAILs: the def is not ptr-kind |
| KIND-04 | production `ptr_kinds` propagates a passed stack address to the callee's parameter lane | drop the caller-to-callee propagation from `ptr_kinds` | pin FAILs: the parameter is not ptr-kind |
| TYPES-24 | hike-sign stamps the PLT-trampoline classification on the sub term (`sign_sub`: self-targeted, contains a real call, reads no non-return/non-SP register — from the same liveness run as the signature); the emitter's `is_self_call_stub` reads the stamp | change the stamp condition in `src/hike_types.ml` to `if false then` | TYPES-24 red: the self-call stub carries no stamp |
