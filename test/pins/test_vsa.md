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
| VSA-32 | `constrain_edge` + the flag def chain — the mixed-def flag IS refined to `{1}` on the taken edge | make the flag-guard arm answer `env` unchanged | VSA-32 red: `{1}` not the taken flag value |
| VSA-34 | `Cbat_call_effects.transfer` (`src/cbat_vsa/cbat_call_effects.ml:31`) — the post-call reload reads TOP | keep the aliased cell live across the call (skip the escape/kill) | VSA-34 red: `find_word 64` is not top |
| VSA-36 | the call's SP restore — `RSP` is preserved across the call | drop the `RSP`-preserved arm from the preserved set | VSA-36 red: `RSP ≠ {0x2000}` |
| VSA-37 | the call's frame-keep — `RBP` is preserved across the call | treat `RBP` as caller-saved | VSA-37 red: `RBP ≠ {0x100}` |
| VSA-52 | `Cbat_transfer.denote_def` — `RAX := high:0[RAX]` after a call denotes and the fixpoint completes, `RAX = top(64)` | make the zero-size `HIGH` cast raise in `denote_def` | VSA-52 red: the fixpoint raises / `RAX ≠ top` |
| VSA-57 | `static_graph_vsa` / `Cbat_forward.denote_block` — the counter-shift loop's trace partition (iterate ⊆ [0,4], exit min ≥ 5) | drop the taken-edge refinement so the body IN-state is unrefined | VSA-57 red: `max_elem c_iter > 4` / `min_elem c_exit < 5` |
| VSA-60 | `Cbat_vsa.init_sol` (`cbat_vsa.ml:49`) — the entry `RSP` anchor is the symbolic segment base at offset 0 (`StackOff{0}`) | seed the entry `RSP` with `Ws.top 64` instead of `stack_word_i64 0` | VSA-60 red: `find_word 64` ≠ `stack_word_i64 0` |
| VSA-66 | the round-down idiom's two-name spelling: `[v1 := x >> k] … `[v2 := v1 << k]` — a regular virtual temp `[t := x]` with a local SSA version is inserted before the shift, the shift-back becomes `[t & ~(2^k - 1)]`, the shift def itself is untouched (its flag readers stay exact) | make the pairing ignore a lhs redefinition between the defs (the stale-map bug), or mint the temp at version 0 (the entry-lane bug) | VSA-66 red: the temp/mask shape assert fails, or the temp is not a versioned virtual |
| VSA-67 | `Hike_vsa.fixpoint` arms ONE `Vsa.with_images` bracket around the whole fused solve (the phases, the completion's rewrites, and the `stamp_envs_of_sol` replay), so a load from a threaded section address denotes the image bytes | replace `Vsa.with_images images` with `Vsa.with_images []` in `fixpoint` (the one bracket) | VSA-67 red: the load's def is `top`, not `{0x2d}` |
| VSA-68 | `Hike_vsa.start`/`resume` — a call whose callee is `Blocked` has a bottom continuation, the phase pauses with that callee and its solution as the seed, and resuming under the callee's summary reaches the same per-block environments as a cold solve that knew the summary from the start | give a blocked call the `Summary None` transfer instead of bottom | VSA-68.seed FAILs (the continuation is reached), and VSA-68.equal FAILs (a pessimistic seed keeps RSI/RBX top after resume) (review) |
| VSA-69 | Slice facts: a guard on `low:8[x]` bounds the later read of `low:8[x]` while the owner `x` keeps its wide hull. | Drop the slice fact when the read block receives it. | VSA-69.read FAILs: the byte read exceeds `0x25`. |
| VSA-70 | Slice facts: the extract form `bits 15..8` is bounded the same way as a low byte. | Handle only `LOW` casts, not `Extract`, when recording slices. | VSA-70 FAILs: the extracted byte is unbounded. |
| VSA-72 | Slice facts: a redefinition of the owner discards the fact. | Carry slices across a def of their owner. | VSA-72 FAILs: the redefined owner keeps the old byte bound. |
| VSA-73 | Slice facts: a call that clobbers the owner discards the fact. | Preserve slices across a call that writes the owner. | VSA-73 FAILs: the caller's byte bound survives the call. |
| VSA-74 | Slice facts: a second guard on the whole register keeps the byte fact. | Let a whole-word guard drop the slice facts. | VSA-74 FAILs: the byte read is unbounded after the second guard. |
| VSA-75 | Slice facts: after a merge the fact is kept only when both paths carry it, as the join of both. | Keep a slice fact when only one incoming path carries it. | VSA-75.one FAILs: the unguarded path's bound leaks into the join. |
| VSA-76 | Slice facts: a loop guarded by a byte converges with the byte bounded in the body. | Drop slice facts at the loop header. | VSA-76 FAILs: the body's byte read loses its bound. |
| VSA-77 | Waking an unreachable call preserves bottom at its continuation. | Seed the woken call with a non-bottom state. | VSA-77 FAILs: the continuation is not `AI.bottom`. |
| VSA-78 | Redefining a word with the same value keeps the state's physical identity. | Rebuild the state unconditionally on `add_word`. | VSA-78 FAILs: `st1 != st2`. |
| VSA-79 | A definition drops the owner's slices, and they stay gone after a delivery and a phi copy. | Preserve slices across `add_word`, `deliver`, or `copy_slices`. | VSA-79.owner-slices or VSA-79.copy FAILs. |
| VSA-80 | A delivery keeps only the target's phis, leaves its memory, and drops the source's own values. | Deliver every non-bottom word, not just the kept phis. | VSA-80.stale/source-only/free/target-local FAIL. |
| VSA-81 | A two-predecessor join keeps only target phi values; a source-only value common to both edges does not reappear. | Merge every source phi into the join. | VSA-81 source-only-dropped FAILs: the common value reappears. |
| VSA-82 | After SSA construction a non-entry block has no free word input outside its phi lhs set. | Omit phi placement for a join. | VSA-82 offenders FAIL: the missing phi is detected. |
| VSA-83 | The entry's index-0 ABI input is seeded, and a free word input on the entry is exempt from the join check. | Do not seed entry ABI inputs, or apply the join check to the entry. | VSA-83.entry-seed/entry-def FAILs. |
| VSA-84 | Both outgoing edges agree with an ordered independent replay of the source block: edge memory and scalar phi values match. | Denote the source once and reuse the result for both edges. | VSA-84 edge-memory/scalar FAILs. |
| VSA-85 | A changed IN state refreshes the cached loop edge and exit value. | Cache the exit phi value across the loop revisit. | VSA-85 exit-value FAILs: the exit is not `{5}`. |
| VSA-86 | A revisited branch's successors receive separate taken and fallthrough refinements. | Apply one edge's refinement to both successors. | VSA-86 taken/fallthrough FAILs. |
| VSA-87 | Read-only inputs stay in the environment without duplicate cells; delivery drops them; an absent variable reads top. | Deliver read-only inputs, or treat an absent variable as non-top. | VSA-87 read-only-input or absent-variable FAILs. |
