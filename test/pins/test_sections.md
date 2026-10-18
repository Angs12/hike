# Pins — test_sections (module `sections`, prefix `SEC`)

One row per pin. Completeness: the id column equals
`dune exec test/unit/test_sections.exe -- list`.

Production `src/` is never touched; recipes are the textual change that
disables the mechanism, re-demonstrated by review when it changes.
Red evidence is the assertion that flips under the recipe.

The range/projection/claim pins (SEC-01..SEC-54) exercise the pure
mechanism and the fixture chain; the regression pins (SEC-55..SEC-68)
carry the Sections-owned C1/C3/C4b, A1/A4c, R12 and fp-GPR S2/S2b/S3
assertions. SEC-76/77/78 pin Phase 1's exact outgoing-store window, the
absence of a window member when a call has no stack arguments, and shared
storage for a frame pointer that escapes.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| SEC-07 | a bottom denotation claims like a failed query (no tag, full-range portions); a def-anchored bottom is incomplete evidence on a reachable path, so the access keeps its memory form | make the bottom arm return `(Some Tag.Dead, [])` (the removed dead-class row) | SEC-07 red: the bottom denotation must produce non-empty portions and no tag |
| SEC-08 | plain TOP claims Stack `[entry+min_int,entry+7]` + Args `[entry+8,max]`, no tag | clamp a plain top like a symbolic top | SEC-08 red: shape is not the two-portion plain claim |
| SEC-09 | symbolic TOP claims `Stack [floor,entry-1]` with `Stack_unbounded` | let a symbolic top fall through to the plain full-line claim | SEC-09 red: `t ≠ Stack_unbounded` / wrong bounds |
| SEC-10 | a plain TOP contributes no data-space portion | let the plain top add a `Data`/`Rodata` portion | SEC-10 red: `for_all ps ∈ {Stack,Args}` fails |
| SEC-13 | an overflowed unsigned expansion saturates at the domain top (`Sec` hi = -1) | wrap `hi+w-1` without saturation | SEC-13 red: `pt_hi ≠ -1` / unordered range |
| SEC-14 | a signed expansion at the line top saturates at `max_int` (Args) | wrap the signed `lo+w-1` at the Args ceiling | SEC-14 red: no Args portion at `max_int` |
| SEC-15 | a crossing interval splits into Stack + Args portions, both identity | emit one portion across the boundary (no split) | SEC-15 red: `length ps ≠ 2` / section wrong |
| SEC-16 | a bounded single-space symbolic read is eligible | clear `pt_elig` on the symbolic arm | SEC-16 red: `not p.pt_elig` |
| SEC-17 | a plain numeric stack-band hull has no stack attribution | classify plain numeric bands as Stack | a plain floating-point bit pattern acquires stack portions |
| SEC-18 | a resolved address basis wholly in one span proves its occupied portion | discard the synthetic address basis | SEC-18 red: the portion is ineligible |
| SEC-19 | a symbolic range crossing the retaddr boundary is identity on both sides | mark crossing portions eligible | SEC-19 red: some `p.pt_elig` |
| SEC-20 | the same denotation without a resolved address basis contributes identity | grant eligibility without a section basis | SEC-20 red: the portion is eligible |
| SEC-21 | a plain access straddling a span edge contributes only the intersecting portion, identity | emit the whole access or mark it eligible | SEC-21 red: bounds or `pt_elig` differ |
| SEC-27 | a TOP write + known read share `Stack_residue` | keep the TOP write out of the merge (spurious Region) | SEC-27 red: storage ≠ `Stack_residue` |
| SEC-28 | the TOP write also claims the Args space (`Stack_residue`) | scope the TOP write to Stack only | SEC-28 red: Args range is unowned |
| SEC-29 | a different sub's tree keeps its own `Stack_region 1` | key sub trees by range instead of tid | SEC-29 red: the other sub's range is the shared residue |
| SEC-31 | an escaped SP-derived extent takes `Stack_residue` | drop the escape member from the merge | SEC-31 red: storage ≠ `Stack_residue` |
| SEC-32 | the escape member survives finalization with `m_def = None` and `m_identity` | drop def-less identity members at finalization | SEC-32 red: no such member on the tree |
| SEC-34 | the retaddr bytes' component takes `Stack_residue` | classify the retaddr read as a normal bounded read (Region) | SEC-34 red: storage ≠ `Stack_residue` |
| SEC-38 | a store demotes its own cell to `Stack_residue` | let the read keep the slot across a store | SEC-38 red: storage ≠ `Stack_residue` |
| SEC-39 | the neighboring cell keeps its own `Arg_slot 1` | promote the store's demotion across cells | SEC-39 red: storage ≠ `Arg_slot 1` |
| SEC-40 | `stamp_tags` lands `Stack (entry-16,entry-16)` on the known read | drop the `set_sec_tag` call in `stamp_tags` | SEC-40 red: tag is `None` / wrong bounds |
| SEC-41 | `stamp_tags` lands `Args (entry+12,entry+12)` on the intra-cell read | as SEC-40 | SEC-41 red: tag is `None` / wrong bounds |
| SEC-42 | a TOP-addressed store carries no tag | stamp the unknown-provenance def too | SEC-42 red: tag is `Some _` |
| SEC-44 | `global_comps_of` — a resolved in-span read is a one-word component typed 8 | discard the synthetic address basis in the data collector | SEC-44 red: no/short component |
| SEC-45 | the same read without a resolved address basis converts to nothing | emit a component without a section basis | SEC-45 red: list nonempty |
| SEC-46 | a sub-word read's component covers the whole word (word hull) | key the component by bytes instead of words | SEC-46 red: `lo_w/hi_w` ≠ 0 |
| SEC-47 | same-word reads merge; agreeing widths type the tile | fail to merge same-word facts | SEC-47 red: two components |
| SEC-48 | disagreeing widths collapse the component's type to bytes (typed_w 1) | keep the first width instead of the byte floor | SEC-48 red: `typed_w ≠ 1` |
| SEC-49 | disjoint words stay separate; ids ascend by (section, position) | order components by discovery instead of position | SEC-49 red: id/word mapping differs |
| SEC-50 | a copy-reloc span is one whole-span region; the slot keeps the through lane | carve the copy-reloc span into word components | SEC-50 red: `global_comps_of` nonempty / no whole span |
| SEC-51 | `top_claim Query_failed` is the plain full-line claim | special-case a non-plain claim for `Query_failed` | SEC-51 red: `plain` fails |
| SEC-52 | `top_claim Foreign` is the plain full-line claim | special-case a non-plain claim for `Foreign` | SEC-52 red: `plain` fails |
| SEC-53 | `top_claim Unbounded_stack` reaches the floor below the entry | answer the plain claim for `Unbounded_stack` | SEC-53 red: `to_floor` fails |
| SEC-55 | the narrow `r16` store converts to `region_mem 1` at the storage base (`stack_r1_ptr`), keeping its width | make the region rewrite width-sensitive (skip narrow stores) | SEC-55 red: the narrow store's mem is not `region_mem 1` |
| SEC-56 | the pre-call caller-frame cell `[RSP-8]` holds `{0xAA}` | break the store denotation at the frame cell | SEC-56 red: value ≠ `{0xAA}` |
| SEC-57 | the pre-call outgoing slot `[RSP+16]` holds `{0xBB}` | drop the outgoing-slot store from the block | SEC-57 red: value ≠ `{0xBB}` |
| SEC-58 | a Stack address in the call-read lane marks the frame escaped, so both the local and outgoing Stack cells clear | disable the frame-escape bit in `cbat_call_effects.transfer` | SEC-58 red: the post-call cells are not TOP |
| SEC-60 | the widened (Infinite-class) store's component takes `Stack_residue`, never Region | treat the widened member as a bounded Region | SEC-60 red: storage ≠ `Stack_residue` |
| SEC-61 | the constant cell joins the widened member's `Stack_residue` (together, not Region) | split the widened member from the constant cells | SEC-61 red: `[entry-16,entry-9]` storage ≠ `Stack_residue` |
| SEC-65 | `layout_of_tree` — an 8-byte occupied span allocates 16 (align16 once, no width factor) | multiply the size by the access width in the layout rule | SEC-65 red: `regions ≠ [ (1, (entry-8,entry-1), 16) ]` |
| SEC-66 | `S2`: an untagged heap-RBP store does not degrade the sub (rsp cell keeps Region) | classify stack-ness by the base register's name | SEC-66 red: storage ≠ `Stack_region 1` |
| SEC-69 | a runtime-sized allocation is ordinary stack arithmetic: the band store's origin is `Stack` and its one portion reaches the floor, the layout sets `runtime_residue`, and the frame cells share the residue | bind a Stack-TOP claim only down to a fixed depth | SEC-69 red: the portion bound, the flag or the residue storage differs |
| SEC-70 | a frame store beside a runtime-sized allocation keeps its one exact Stack portion | split a frame claim around the allocation | SEC-70 red: the portion-count/bounds assert fails |
| SEC-71 | B2a: the residue's window reserve is the def-backed members' proven reach — the call escape does not size it. | textually invert the pinned contract in `Hike_sections` | pin FAILs under that inversion (re-demonstrated by review) |
| SEC-72 | storage selection: a finite residue depth above 64 KiB sizes the residue exactly, `runtime_residue` false | clamp `member_below` to 64 KiB | SEC-72 red: the residue depth is 64 KiB |
| SEC-73 | storage selection: a depth beyond `frame_alloca_max` sets `runtime_residue` | drop the depth test in `member_runtime` | SEC-73 red: flag false |
| SEC-74 | storage selection: an unbounded stack extent sets `runtime_residue` | claim a bounded range for `Unbounded_stack` | SEC-74 red: flag false |
| SEC-75 | storage selection: a bounded frame keeps allocas, `runtime_residue` false | set the flag for every residue | SEC-75 red: flag true |
| SEC-76 | the caller-window member is exactly the hull of two aligned outgoing stack-argument stores | restore the fixed `[SP-8, SP+64 KiB+64]` call member | SEC-76 red: the Args member bounds differ from the two stored bytes |
| SEC-77 | two local Stack stores and a call with no outgoing stack arguments retain two regions and need no incoming window | add an unconditional call-window member | SEC-77 red: the layout has one residue or `window_param` is true |
| SEC-78 | a stack pointer passed in a lane claims shared storage for the caller frame | limit the escape identity member to the pointer's own offsets | SEC-78 red: adjacent frame cells select different storage |
