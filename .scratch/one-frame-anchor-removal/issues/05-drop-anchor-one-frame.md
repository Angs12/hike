# 05: Drop the anchor — one flat frame per sub (wide refactor — expand–contract)

**What to build:** The current emission model has each sub allocate a
`%frame` alloca with an `%anchor` GEP at offset `N - 8`. Every
inttoptr arithmetic in the lifted IR is computed from `anchor_i64`
(the ptrtoint of the anchor). The per-region alloca split
(`stack_rN`) is a per-region GEP into `%frame` or into a per-region
alloca. The fix replaces this with **one flat frame per sub**: no
`%anchor` GEP, no `anchor_i64`, no per-region split. The frame base
IS the entry RSP. Stack accesses are computed as
`GEP %frame, lo` for static offsets (the VSA's `Range(lo, lo)`)
or `inttoptr (frame_i64 + VSA_offset) to ptr` for runtime
expressions (the VSA's `Unbounded` / `Infinite` / non-singleton
`Range`). The `region_split_plan` gate is gone; every precise
sub is emitted with the flat frame.

This is a **wide refactor**: `build_frame_anchor`, `degraded_dims`,
`create_static_mem_access`, `rebase_addr`, `create_sub`'s
`region_split_plan` gate, and the `stack_rN` allocation all change.
Expand–contract:

1. **Expand**: add a new `build_flat_frame` lane alongside
   `build_frame_anchor`. `create_sub` gains a new `?flat_frame`
   parameter (default `false`); the new lane is selected by the
   ticket's tests. Both lanes coexist; the old lane is the default.
2. **Migrate**: route the precise subs (the `is_precise = true`
   case in `create_sub`) through the new lane; verify each
   precise sub's gates (per-sub `run_semantic_all.sh` on the
   affected binaries: `nested_struct`, `va_arg_mixed`,
   `va_arg_vacopy`, `variadic`).
3. **Contract**: route the degraded subs (the `is_precise = false`
   case) through the new lane; retire `build_frame_anchor`,
   `degraded_dims`, `region_split_plan`, the per-region `stack_rN`
   allocation, and the `?flat_frame` parameter (now the default).

**Blocked by:** T02, T03, T04. The flat-frame lane needs the VSA's
value-tracking (T02) to resolve value-typed addresses; the
per-call alloca (T03) for va_list args; the VSA-subsumes-relevance
(T04) to remove the per-region split's tag dependency.

**Status:** ready-for-agent (after T02, T03, T04 land).

- [ ] Expand phase: `build_flat_frame` allocates one `[N x i8]`
  alloca (no anchor); `create_sub` accepts a `?flat_frame`
  parameter; the new lane is selected by the ticket's tests. Old
  `build_frame_anchor` / `region_split_plan` / `stack_rN` code
  unchanged.
- [ ] Migrate phase: precise subs route through `build_flat_frame`;
  the per-region `stack_rN` allocation is replaced with the flat
  frame; `out_nested_struct` (the by-value struct copy) PASSes
  because the struct is now contiguous in one alloca.
- [ ] Contract phase: degraded subs also route through
  `build_flat_frame`; `build_frame_anchor` and `region_split_plan`
  deleted; the per-region allocation deleted; `?flat_frame`
  parameter removed.
- [ ] `dune runtest` green; no regressions.
- [ ] `run_corpus.sh` 31/31 rc=0.
- [ ] `check_allocas.sh` 124/0.
- [ ] `run_semantic_all.sh` — **31/31 PASS** (all 3 remaining
  failures recovered: nested_struct, va_arg_vacopy, variadic).
- [ ] `AGENTS.md` §Current validation state updated with the
  one-frame architecture note and the new gate numbers.

**Notes:** This ticket is the LAST in the workstream. The final
gate target is 31/31 `run_semantic_all.sh` (recovering the 3
pre-existing failures). The 3 LM F1/F2c unit failures remain
(unrelated landmark-widening work).
