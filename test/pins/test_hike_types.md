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
| TYPES-12 | `compute_sub_sig`: SP, the thread pointer, and callee-saved registers are filtered from argument lanes. | In the `filter`, drop the `is_callee_saved`/`Abi.sp`/`thread_pointer` disjuncts. | TYPES-12 FAILs: RSP/RBX/FS_BASE become args. |
| TYPES-13 | `compute_sub_sig`: intrinsic targets and explicitly registered slot/argument variables are filtered from argument lanes. | In the `filter`, drop the intrinsic-name or synth-table classification checks. | TYPES-13 FAILs: the promoted lanes become args. |
| TYPES-16 | `compute_sub_sig`: a `window_param` layout carries the caller window as a pointer `In` lane. | In `compute_sub_sig`, drop the `window_arg` append (`args @ []`). | TYPES-16 FAILs: the window lane is absent. |
| TYPES-17 | `compute_sub_sig`: an emittable intrinsic takes its free vars `In` and its own defs `Out`. | In the intrinsic branch, skip the def scan for returns (return the target's `rets`). | TYPES-17 FAILs: the intrinsic's `Out` lane is absent. |
| TYPES-18 | `compute_sub_sig`: every internal sub carries the ABI's return registers as Out lanes (the list is the ABI's, so extending it does not break the pin); the boundary (the C entry) and unknown targets do not. | In `compute_sub_sig`, drop the `vector_return_reg` from the carriers (or take the `fixed_signature` branch for every sub). | TYPES-18 FAILs: YMM0 is missing (a boundary-only signature). |
| TYPES-22 | A named external call receives the synthetic parameter-register ABI even when its target sub is not in the filtered program. | In `is_native_call`, classify every generated no-return direct target as a real call. | TYPES-22 FAILs: the external-call sub has no synthetic argument lanes. |
| TYPES-23 | A canonical direct `hike_return` edge is not a native call and does not add synthetic parameter lanes. | In `is_native_call`, count the canonical direct return as a call. | TYPES-23 FAILs: the terminal-return sub has synthetic argument lanes. |
| KIND-01 | a def computing a stack address is ptr-kind (its denotation is stack-resident) — the emitter's pointer argument depends on it | drop the denotation seed from `ptr_defs` | pin FAILs: the def is not ptr-kind |
| KIND-05 | `ptr_defs` facts are SSA versions: a pointer parameter's entry version does not type the register's later integer versions | in `ptr_defs`'s `is_ptr`, also accept `Core.Set.mem ptrs (Var.base v)` | KIND-05 FAILs: RDI.1 and RBX.1 become pointers |
| KIND-04 | production `ptr_kinds` propagates a passed stack address to the callee's parameter lane | drop the caller-to-callee propagation from `ptr_kinds` | pin FAILs: the parameter is not ptr-kind |
| TYPES-24 | hike-sign stamps the PLT-trampoline classification on the sub term (`sign_sub`: self-targeted, contains a real call, reads no non-return/non-SP register — from the same liveness run as the signature); the emitter's `is_self_call_stub` reads the stamp | change the stamp condition in `src/hike_types.ml` to `if false then` | TYPES-24 red: the self-call stub carries no stamp |
| TYPES-26 | `sign_sub`: a declaration (bodyless, trampoline) carries the machine convention as its signature: `Abi.param_regs` as `In` args, the return lanes as rets; `Model.call_lanes` and the emitter read it off the sub. | In `compute_sub_sig`, drop the `Model.is_declared` arm. | TYPES-26 FAILs: the bodyless declaration has no argument lanes. |
| TYPES-27 | A return lane follows the version it returns at an exit (`ptr_returns`: an exit no version reaches, as in a trampoline, is no evidence) and `retype_sub` types an output lane by `ptr_rets` alone, so a pointer argument in the same register leaves the return lane an integer. | Restore the base-register fallback in `ptr_returns` (`Option.value ~default:r`), or make `retype_sub`'s `map_arg` map a return lane's lhs through `ptr_vars`. | TYPES-27 FAILs: the RDX return lane becomes a pointer. |
| TYPES-28 | Use-based kinds: a version used as a `Load`/`Store` address is a pointer (a backward `Hike_bir_flow` pass joined with the provenance pass in `ptr_defs`); the loaded value stays an integer. | In `ptr_defs`, make `versioned` false (no use-seeding). | TYPES-28 FAILs: the address versions are integers. |
| TYPES-29 | An address `v := w + 8` with no evidence for `w` (no pointer, static/address leaf or module base) names no base: `w` stays an integer and the access is emitted through `inttoptr`. | In `bases`, restore a fallback that picks the one unseen operand as base. | TYPES-29 FAILs: `w` becomes a pointer. |
| TYPES-30 | A callee's entry version used as a store address types its parameter lane a pointer, with no direct caller to prove it (`redirect`). | In `ptr_defs`, make `versioned` false. | TYPES-30 FAILs: the lane stays an integer. |
| TYPES-31 | A `v1 + v2` address of two bare vars names no base: neither addend becomes a pointer. | In `bases`, return every unseen spine var in the no-base fallback. | TYPES-31 FAILs: the addends become pointers. |
| TYPES-32 | The use rule is per SSA version: a later version of the same register, and a narrower value, stay integers. | In `ptr_defs`'s `use_ok`, accept any version of a pointer's base register. | TYPES-32 FAILs: the later version becomes a pointer. |
| TYPES-33 | An address's base is read off the denotation, not the shape: in `RSP + (i - 72 + 104)` the stack operand is the base, the loop index `i` stays an integer, and the access is a GEP off the stack base with no `inttoptr`. | In `bases`, return every spine var, not only the base leaves. | TYPES-33 FAILs: `i` becomes a pointer. |
| TYPES-34 | With no base evidence (no pointer, static/address leaf or module base) an address names no base: `load + {0, 8}` leaves both operands integers and the access goes through `inttoptr`. | In `bases`, restore a fallback that picks the one unseen operand as base. | TYPES-34 FAILs: the loaded value becomes a pointer. |
| TYPES-35 | A module address is a base: in `rodata + idx` (the address is a copy of a module address, idx a phi of `{0, 8}`) the address is a GEP off the module global with no `inttoptr`, and `idx` stays an integer. | In `bases`, drop the module-origin clause of `module_base`. | TYPES-35 FAILs: the address is `add` + `inttoptr`. |
| TYPES-36 | pointer retyping preserves indirect calls, their continuations and indirect jumps with their pointer target type and identity | use BAP that drops non-`Imm` indirect destinations | transfer kind changes and the pin fails |
