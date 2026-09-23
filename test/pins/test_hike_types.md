# Pins: Hike_types

Module `src/hike_types.ml` (no interface; all let-bindings visible).
One row per pin in `test/unit/test_hike_types.ml` (ids `TYPES-01`..`TYPES-20`).

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
| TYPES-01 | `free_vars` drops memory-typed vars from `Sub.free_vars` and keeps registers. | In `src/hike_types.ml` `free_vars`, drop the `not @@ Model.is_mem` filter. | TYPES-01 FAILs: the mem var joins the list. |
| TYPES-02 | `fp_returning`: a YMM def on the epilogue path (an indirect call with no return) is an FP return. | In `fp_returning`, make `is_epilogue` always `false` (or drop the `Seq.exists`). | TYPES-02 FAILs: the FP sub answers `false`. |
| TYPES-03 | `fp_returning`: an integer return register (`RAX`) on the epilogue path is not an FP return. | In `fp_returning`, drop the final `is_vector_param_reg` test (return `return_path_defs <> []`). | TYPES-03 FAILs: the integer sub answers `true`. |
| TYPES-04 | `fp_returning`: a value def off the epilogue path is not a return at all. | In `fp_returning`, treat every value-reg def as a return path (drop the `is_epilogue` filter). | TYPES-04 FAILs: the no-epilogue sub answers `true`. |
| TYPES-05 | `tag_lane`: a plain `In` register lane is left untagged. | In `tag_lane`, drop the pointer guard (always `set_ptr_arg`). | TYPES-05 FAILs: the lane becomes a pointer. |
| TYPES-06 | `tag_lane`: a `Both` intent lane is a pointer (an address lane). | In `tag_lane`, drop the `Arg.intent a = Some Both` arm. | TYPES-06 FAILs: the `Both` lane is untagged. |
| TYPES-07 | `tag_lane`: a memory-typed lhs lane is a pointer (its storage). | In `tag_lane`, drop the `Model.is_mem v` arm. | TYPES-07 FAILs: the mem lane is untagged. |
| TYPES-08 | `tag_lane`: the caller-window lane is a pointer. | In `tag_lane`, drop the `Model.is_window_var v` arm. | TYPES-08 FAILs: the window lane is untagged. |
| TYPES-09 | `compute_sub_sig`: the x86_64 target returns `RAX`/`RDX` `Out`; a lane-free, call-free sub has no args. | In `compute_sub_sig`, replace the `Theory.Target.matches … "x86_64-gnu-elf"` test with `false`. | TYPES-09 FAILs: the return list empties. |
| TYPES-10 | `compute_sub_sig`: an unknown target answers no returns (the target check is the switch). | As TYPES-09 but make the target test always `true`. | TYPES-10 FAILs: the unknown target gains RAX/RDX. |
| TYPES-11 | `compute_sub_sig`: free registers become `In` args ordered by parameter rank (RDI before RSI). | In the final `args` fold, drop the `Base.List.sort ~compare` (keep set order). | TYPES-11 FAILs: the order or membership changes. |
| TYPES-12 | `compute_sub_sig`: SP, the thread pointer, and callee-saved registers are filtered from argument lanes. | In the `filter`, drop the `is_callee_saved`/`Abi.sp`/`thread_pointer` disjuncts. | TYPES-12 FAILs: RSP/RBX/FS_BASE become args. |
| TYPES-13 | `compute_sub_sig`: intrinsic-target and promoted (`hike_slot`/`hike_arg`) names are filtered from argument lanes. | In the `filter`, drop the intrinsic-name/`hike_slot`/`hike_arg` disjuncts. | TYPES-13 FAILs: the promoted lanes become args. |
| TYPES-14 | `compute_sub_sig`: a call with no argument lanes takes the full parameter-register signature (14 SysV lanes). | In `compute_sub_sig`, delete the `is_plt_sig` branch (leave `args = []`). | TYPES-14 FAILs: the call-carrying sub has no args. |
| TYPES-15 | `compute_sub_sig`: `@main` keeps the fixed `RDI`/`RSI` signature. | In `Model.fixed_signature`, drop the `Tid.name … = "@main"` disjunct. | TYPES-15 FAILs: `@main` falls to the PLT/else shape. |
| TYPES-16 | `compute_sub_sig`: a `window_param` layout carries the caller window as a pointer `In` lane. | In `compute_sub_sig`, drop the `window_arg` append (`args @ []`). | TYPES-16 FAILs: the window lane is absent. |
| TYPES-17 | `compute_sub_sig`: an emittable intrinsic takes its free vars `In` and its own defs `Out`. | In the intrinsic branch, skip the def scan for returns (return the target's `rets`). | TYPES-17 FAILs: the intrinsic's `Out` lane is absent. |
| TYPES-18 | `compute_sub_sig`: an FP-returning sub appends the `YMM0` `Out` lane to the integer returns. | In `compute_sub_sig`, drop the `if fp_returning … then rets @ [ymm0]` branch. | TYPES-18 FAILs: YMM0 is missing. |
| TYPES-19 | `sign_program`: the computed `(rets @ args)` lanes land on the sub's own `arg` terms, intent and pointer tag included. | In `sign_program`, call `Model.set_sig sub rets` (drop the args) or `set_sig` without `compute_sub_sig`. | TYPES-19 FAILs: the arg terms no longer match `rets @ args`. |
| TYPES-20 | `run`: the project entry signs the project's own program with the project's target. | In `run`, drop the `Project.map_program … sign_program` (return `proj` unchanged). | TYPES-20 FAILs: the sub carries no `arg` terms. |
