# Pins — test_sections (module `sections`, prefix `SEC`)

One row per pin. Completeness: the id column equals
`dune exec test/unit/test_sections.exe -- list`.

Production `src/` is never touched; recipes are the textual change that
disables the mechanism, re-demonstrated by review when it changes.
Red evidence is the assertion that flips under the recipe.

The range/projection/claim pins (SEC-01..SEC-54) exercise the pure
mechanism and the fixture chain; the regression pins (SEC-55..SEC-68)
carry the Sections-owned C1/C3/C4b, A1/A4c, R12 and fp-GPR S2/S2b/S3
assertions.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| SEC-01 | `Hike.Sections.range_of_denotation` — the occupied-byte extent is `lo .. lo+width-1` (`src/hike_sections.ml`) | drop the `+ width - 1` in the occupied-hi computation | SEC-01 red: the 1-byte portion's `pt_hi ≠ entry-8` |
| SEC-02 | occupied extent of an 8-byte singleton | same recipe as SEC-01 | SEC-02 red: `pt_hi ≠ entry-1` |
| SEC-03 | occupied extent of a ranged hull at hwidth 4 | same recipe as SEC-01 | SEC-03 red: `pt_hi ≠ entry-5` |
| SEC-04 | occupied extent of a 4-byte singleton | same recipe as SEC-01 | SEC-04 red: `pt_hi ≠ entry-1` |
| SEC-05 | the retaddr row: `Stack (entry,entry)` tag and the `[entry,entry+7]` portion | return the Args space for offset 0 (shift the entry split) | SEC-05 red: tag/portion section or bounds differ |
| SEC-06 | the args row: `Args (entry+8,entry+8)` tag, `[entry+8,entry+15]` portion | map offset +8 to Stack instead of Args at the entry split | SEC-06 red: `pt_sec ≠ Args` |
| SEC-07 | bottom denotation yields `Dead` and no portion | make the bottom arm return a `Stack` portion instead of `None, []` | SEC-07 red: pattern `Dead, []` fails |
| SEC-08 | plain TOP claims Stack `[entry+min_int,entry+7]` + Args `[entry+8,max]`, no tag | clamp a plain top like a symbolic top | SEC-08 red: shape is not the two-portion plain claim |
| SEC-09 | symbolic TOP clamps to `Stack [entry-65536,entry-1]` with `Stack_unbounded` | let a symbolic top fall through to the plain full-line claim | SEC-09 red: `t ≠ Stack_unbounded` / wrong bounds |
| SEC-10 | a plain TOP contributes no data-space portion | let the plain top add a `Data`/`Rodata` portion | SEC-10 red: `for_all ps ∈ {Stack,Args}` fails |
| SEC-11 | `compare_point` orders the full data domain `[0,2^64-1]` | use signed comparison for data sections | SEC-11 red: `compare_point … ≥ 0` |
| SEC-12 | the unsigned seam orders the high half above `2^63-1` | same signed-data recipe as SEC-11 | SEC-12 red: `compare_point … ≥ 0` |
| SEC-13 | an overflowed unsigned expansion saturates at the domain top (`Sec` hi = -1) | wrap `hi+w-1` without saturation | SEC-13 red: `pt_hi ≠ -1` / unordered range |
| SEC-14 | a signed expansion at the line top saturates at `max_int` (Args) | wrap the signed `lo+w-1` at the Args ceiling | SEC-14 red: no Args portion at `max_int` |
| SEC-15 | a crossing interval splits into Stack + Args portions, both identity | emit one portion across the boundary (no split) | SEC-15 red: `length ps ≠ 2` / section wrong |
| SEC-16 | a bounded single-space symbolic read is eligible | clear `pt_elig` on the symbolic arm | SEC-16 red: `not p.pt_elig` |
| SEC-17 | a plain band hull is identity (no StackOff proof) | set `pt_elig = true` on the plain arm | SEC-17 red: `p.pt_elig` |
| SEC-18 | a rip-tagged plain access wholly in one span is the `Sec` proof with occupied bounds | ignore the rip flag when forming `Sec` | SEC-18 red: `t ≠ Sec …` / bounds differ |
| SEC-19 | a symbolic range crossing the retaddr boundary is identity on both sides | mark crossing portions eligible | SEC-19 red: some `p.pt_elig` |
| SEC-20 | the same access without the rip tag contributes identity (`None`) | stamp a `Sec` tag when `rip=false` | SEC-20 red: `t ≠ None` / `p.pt_elig` |
| SEC-21 | a plain access straddling a span edge contributes only the intersecting portion, identity | emit the whole access or mark it eligible | SEC-21 red: bounds or `pt_elig` differ |
| SEC-22 | an interval disjoint from every span contributes no member | clamp a disjoint range into the nearest span | SEC-22 red: `ps ≠ []` |
| SEC-23 | the fixture chain installs (fixpoint converged, nonempty envs) | make `Hike.Vsa.fixpoint` return `None` for the fixture | SEC-23 red: `solved` is false |
| SEC-24 | overlapping stack reads merge into one `Stack_region 1` | disable the overlap merge in `Hike.Sections.attribute` | SEC-24 red: storage ≠ `Stack_region 1` |
| SEC-25 | adjacent-only reads stay separate with ascending ids | merge all regions (drop the overlap test) | SEC-25 red: both ranges get the same region id |
| SEC-26 | the top-write fixtures install | as SEC-23 | SEC-26 red: `solved` is false |
| SEC-27 | a TOP write + known read share `Stack_residue` | keep the TOP write out of the merge (spurious Region) | SEC-27 red: storage ≠ `Stack_residue` |
| SEC-28 | the TOP write also claims the Args space (`Stack_residue`) | scope the TOP write to Stack only | SEC-28 red: Args range is unowned |
| SEC-29 | a different sub's tree keeps its own `Stack_region 1` | key sub trees by range instead of tid | SEC-29 red: the other sub's range is the shared residue |
| SEC-30 | the escape fixture installs | as SEC-23 | SEC-30 red: `solved` is false |
| SEC-31 | an escaped SP-derived extent takes `Stack_residue` | drop the escape member from the merge | SEC-31 red: storage ≠ `Stack_residue` |
| SEC-32 | the escape member survives finalization with `m_def = None` and `m_identity` | drop def-less identity members at finalization | SEC-32 red: no such member on the tree |
| SEC-33 | the retaddr fixture installs | as SEC-23 | SEC-33 red: `solved` is false |
| SEC-34 | the retaddr bytes' component takes `Stack_residue` | classify the retaddr read as a normal bounded read (Region) | SEC-34 red: storage ≠ `Stack_residue` |
| SEC-35 | the args fixture installs | as SEC-23 | SEC-35 red: `solved` is false |
| SEC-36 | full-cell and intra-cell args reads share `Arg_slot 0` | split the intra-cell read into its own slot id | SEC-36 red: storage ≠ `Arg_slot 0` |
| SEC-37 | the args-store fixture installs | as SEC-23 | SEC-37 red: `solved` is false |
| SEC-38 | a store demotes its own cell to `Stack_residue` | let the read keep the slot across a store | SEC-38 red: storage ≠ `Stack_residue` |
| SEC-39 | the neighboring cell keeps its own `Arg_slot 1` | promote the store's demotion across cells | SEC-39 red: storage ≠ `Arg_slot 1` |
| SEC-40 | `stamp_tags` lands `Stack (entry-16,entry-16)` on the known read | drop the `set_sec_tag` call in `stamp_tags` | SEC-40 red: tag is `None` / wrong bounds |
| SEC-41 | `stamp_tags` lands `Args (entry+12,entry+12)` on the intra-cell read | as SEC-40 | SEC-41 red: tag is `None` / wrong bounds |
| SEC-42 | a TOP-addressed store carries no tag | stamp the unknown-provenance def too | SEC-42 red: tag is `Some _` |
| SEC-43 | the data fixture's envs install (`Kb.facts.envs` nonempty) | as SEC-23 | SEC-43 red: `envs` count = 0 |
| SEC-44 | `global_comps_of` — a rip-proved in-span read is a one-word component typed 8 | drop the rip proof requirement in the data collector | SEC-44 red: no/short component |
| SEC-45 | the same read without the rip proof converts to nothing | emit a component without the rip proof | SEC-45 red: list nonempty |
| SEC-46 | a sub-word read's component covers the whole word (word hull) | key the component by bytes instead of words | SEC-46 red: `lo_w/hi_w` ≠ 0 |
| SEC-47 | same-word reads merge; agreeing widths type the tile | fail to merge same-word facts | SEC-47 red: two components |
| SEC-48 | disagreeing widths collapse the component's type to bytes (typed_w 1) | keep the first width instead of the byte floor | SEC-48 red: `typed_w ≠ 1` |
| SEC-49 | disjoint words stay separate; ids ascend by (section, position) | order components by discovery instead of position | SEC-49 red: id/word mapping differs |
| SEC-50 | a copy-reloc span is one whole-span region; the slot keeps the through lane | carve the copy-reloc span into word components | SEC-50 red: `global_comps_of` nonempty / no whole span |
| SEC-51 | `top_claim Query_failed` is the plain full-line claim | special-case a non-plain claim for `Query_failed` | SEC-51 red: `plain` fails |
| SEC-52 | `top_claim Foreign` is the plain full-line claim | special-case a non-plain claim for `Foreign` | SEC-52 red: `plain` fails |
| SEC-53 | `top_claim Unbounded_stack` clamps below the entry | answer the plain claim for `Unbounded_stack` | SEC-53 red: `clamped` fails |
| SEC-54 | the denotation paths land on their claims (`Ws.top`→plain, symbolic→clamped) | diverge the denotation top arm from `top_claim` | SEC-54 red: `plain`/`clamped` fails |
| SEC-55 | the narrow `r16` store converts to `region_mem 1` keeping address and width | make the region rewrite width-sensitive (skip narrow stores) | SEC-55 red: the narrow store's mem is not `region_mem 1` |
| SEC-56 | the pre-call caller-frame cell `[RSP-8]` holds `{0xAA}` | break the store denotation at the frame cell | SEC-56 red: value ≠ `{0xAA}` |
| SEC-57 | the pre-call outgoing slot `[RSP+16]` holds `{0xBB}` | drop the outgoing-slot store from the block | SEC-57 red: value ≠ `{0xBB}` |
| SEC-58 | the caller-frame cell survives the call (frame-keep) | force whole-memory top at the call (`cbat_call_effects.transfer`) | SEC-58 red: post-call value ≠ `{0xAA}` |
| SEC-59 | overlapping constant stores merge into `Stack_region 1` | disable the overlap merge in `attribute` | SEC-59 red: storage ≠ `Stack_region 1` |
| SEC-60 | the widened (Infinite-class) store's component takes `Stack_residue`, never Region | treat the widened member as a bounded Region | SEC-60 red: storage ≠ `Stack_residue` |
| SEC-61 | the constant cell joins the widened member's `Stack_residue` (together, not Region) | split the widened member from the constant cells | SEC-61 red: `[entry-16,entry-9]` storage ≠ `Stack_residue` |
| SEC-62 | the seeded caller-frame cell `[entry RSP-8]` holds `{0xAA}` (RCX-slot variant) | drop the `fp` seed store | SEC-62 red: value ≠ `{0xAA}` |
| SEC-63 | pre-call the neighbor `[-0x18]` holds `{0xAA}` and both slots hold `{0xBB}`,`{0xDD}` | drop an outgoing-slot store | SEC-63 red: one of the three values differs |
| SEC-64 | the neighbor cell outside the slots' extent survives the call untouched | widen the escape range over `[-0x18]` | SEC-64 red: post-call neighbor ≠ `{0xAA}` |
| SEC-65 | `layout_of_tree` — an 8-byte occupied span allocates 16 (align16 once, no width factor) | multiply the size by the access width in the layout rule | SEC-65 red: `regions ≠ [ (1, (entry-8,entry-1), 16) ]` |
| SEC-66 | `S2`: an untagged heap-RBP store does not degrade the sub (rsp cell keeps Region) | classify stack-ness by the base register's name | SEC-66 red: storage ≠ `Stack_region 1` |
| SEC-67 | `S2b` control: the identical sub with an RBX-based heap store is not degraded | classify stack-ness by the base register's name | SEC-67 red: storage ≠ `Stack_region 1` |
| SEC-68 | `S3`: an `[RBP := RSP]` prologue makes RBP sp-derived, so the `[RBP-0x30]` access takes Region | drop the value-based tag on the prologue (name-only) | SEC-68 red: storage ≠ `Stack_region 1` |
