# Pins — test_call_effects

Module: `test/unit/test_call_effects.ml` (group `call_effects`, ids
`CE-01`…`CE-30` (with gaps), merging the `CE1`…`CE10` checks of
`test_cbat/test_forward.ml` (the forward Call_effects family) and the
`C1-1`…`C1-5` checks of `test_cbat/test_vsa.ml`.  Every source `check`
site is carried as one pin; none retired.  Production mechanism:
`src/cbat_vsa/cbat_call_effects.ml` (`Cbat_vsa.Call_effects.transfer` /
`indirect_callee`) with the frame-keep core in
`src/cbat_vsa/cbat_ai_representation.ml` (the sticky frame-escape bit) and
`src/cbat_vsa/cbat_ai_memmap.ml` (`Mem.call_keep`).

There is no `Test_seam` for this pass, so no switch can be
flipped from the test tier.  Production `src/` is never modified.  The
disable recipes below are textual and name the source site to break; the
recorded red is the state that recipe produces (re-demonstrated whenever
the cited mechanism changes).  Every pin builds its own state inside its
closure — no cross-pin state.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| CE-01 | `transfer`'s `Some summary` arm unions the callee's never-written caller-saved GPRs into `preserved` (a `ws` member is kept, a non-member is added unless it is a return reg), so a non-written GPR (`g2`) stays bounded. | In `transfer`, make the `Some ws` arm a no-op: `| Some _ -> preserved`. | CE-01: `Ws.equal (AI.find_word 64 kept g2) (Ws.singleton (w64 2))` fails — `g2` is TOPed (review). |
| CE-02 | `transfer`'s `None` summary arm keeps only the base `preserved` set (unknown/kill-all callee); `g1`/`g2` are TOPed. | In `transfer`, make `None` add all caller-saved GPRs to `preserved` (`| None -> Core.Set.union preserved (Core.Set.of_list (module Var) abi.Hike_abi.caller_saved_gprs)`). | CE-02: `Ws.is_top (AI.find_word 64 killed g1)` fails — the "killed" set retains `g1`/`g2` (review). |
| CE-03 | `AI.call_abstraction_frame` keeps caller-frame cells at/above the highest possible call-time RSP and drops the cells below it (the call-time RSP is `{0x1000}`). The frame boundary `keep_lo` is the SP's segment-relative offset, the namespace Stack cells use. | In `transfer`, bypass the frame keep: `let abs = AI.top in`; alternatively, add the concrete stack base to `keep_lo`. | CE-03: `Ws.equal (ce_reads m 0x2000 kept_frame) (Ws.singleton (w64 42))` fails — the kept cell reads TOP (review). |
| CE-04 | A stack address in a call-read lane sets the sticky frame-escape bit and clears every retained Stack cell. | In `transfer`, force `frame_escaped = false`. | CE-04: the Stack cell at `0x3000` remains `{9}` instead of TOP. |
| CE-06 | A trap leaves the SP untouched — it pops no retaddr. | In `transfer`, add a word to the SP. | CE-06: the trap's SP differs from the stack word it entered with. |
| CE-08 | `indirect_callee` denotes the target exp; a singleton word passes `Cbat_word.to_int64` into `lookup`, then `callee`. | In `indirect_callee`, answer `Summary None` for the singleton arm. | CE-08: the `Summary (Some ws)` arm is never taken, so the match falls to `false` (review). |
| CE-09 | A non-singleton (unbounded or multi-word) target denotation resolves to `Summary None`. | In `indirect_callee`, drop the singleton guard: take `WordSet.min_elem ws` and run `lookup`/`callee` for any non-top set. | CE-09: the match returns the named sub's summary, so the pin's fallthrough `false` fires (review). |
| CE-10 | A bounded singleton whose word `lookup` cannot name (foreign address) resolves to `Summary None`. | In `indirect_callee`, fabricate a summary when `lookup` misses: `~default:(Summary (Some Int.Set.empty))`. | CE-10: the match returns an empty summary, so the pin's fallthrough `false` fires (review). |
| CE-12 | Every word not in `preserved` is TOPed by `call_abstraction_frame`. | In `transfer`, skip the abstraction for words: return `env` unchanged (no `call_abstraction_frame`). | CE-12: `Ws.is_top (AI.find_word 64 env' y)` fails — `y` still reads `{7}` (review). |
| CE-13 | A preserved `RSP` (no push) keeps its value-set; the preserved fold is var-identity based, not name based. | In `transfer`, ignore `preserved`: `let preserved = Var.Set.empty in`. | CE-13: `Ws.equal (AI.find_word 64 e' rsp) (Ws.singleton (w64 0x10))` fails — the RSP is TOPed (review). |
| CE-14 | A call with an unbounded RSP keeps no frame: `call_abstraction_frame` falls back to the whole-memory top when the RSP denotation is not a single word. | In `call_abstraction_frame`, drop the RSP-bound guard and run the frame split regardless of `Ws.cardinal rsp`. | CE-14: the stored `{0x11}` at `[0x10]` survives, so `Mem.equal … (Mem.top …)` fails (review). |
| CE-16 | The frame-keep namespace rule: a plain-top escape cannot name the stack line (a stack address is `Rel`), so it never forces the whole-memory top — the caller's frame survives (`frame_keep` in `src/cbat_vsa/cbat_call_effects.ml` omits non-relative escapes). | In `src/cbat_vsa/cbat_call_effects.ml` `frame_keep`, restore the all-or-nothing escape composition (a `None` range forces top). | CE-16: the frame cells drop (review). |
| CE-18 | Caller-frame survival requires an SP with a stack-family origin. | Use raw numeric SP bounds after `stack_offsets` fails. | The originless SP incorrectly keeps caller-frame facts. |
| CE-19 | A mixed call-read lane containing a Stack leaf sets the sticky bit and clears the whole retained frame. | Ignore Stack leaves when deriving `lane_escapes`. | The Stack cell at `0x3000` remains `{9}` instead of TOP. |
| CE-21 | Once raised, the bit survives a later call with no stack pointer lane. | Clear `AI.escaped` after the first call. | The later call preserves a Stack cell. |
| CE-23 | `Mem.call_keep` drops a Stack cell when its key overlaps an outgoing stack-argument hull. | Replace `Key.overlap` with start-point containment. | A cell straddling the hull survives. |
| CE-24 | Storing a Stack address outside the sub's own below-entry frame raises the bit. | Remove the store escape check in `denote_exp_escaping`. | The post-store state remains contained. |
| CE-25 | Storing a Stack address in the sub's own below-entry frame does not raise the bit. | Treat every Stack-address store as escaped. | The post-store state is marked escaped. |
| CE-26 | The call's outgoing stack-store bindings produce one exact byte hull, and the transfer drops overlapping cells. | Omit `stack_arg_ranges` from `call_site_transfer`. | The outgoing slot at `0x1010` keeps `{5}`. |
| CE-27 | The escape bit joins by OR and participates in equality. | Drop the escape component from join/equality. | The joined states compare equal when they should not. |
| CE-28 | A real call reads the lane value set in a predecessor block, then clears the retained frame. | Limit call facts to integer lanes defined in the call block. | The call post-state lacks the escape bit and retains the local cell. |
| CE-29 | Outgoing SP-relative stores retain their actual addresses when the call later pushes its return address. | Denote every store address in the final call environment. | The hull misses the second outgoing slot. |
| CE-30 | A machine call with a result, a memory effect, and stack arguments: outgoing stores span `[0x1008,0x1017]`, the overlapping retained cell at `0x1010` is dropped, the cell at `0x1018` survives, and the continuation receives a fresh return-lane version. | Skip `stack_arg_ranges` (empty outgoing hull), or keep cells overlapping the hull. | CE-30 FAILs: the hull is empty, `0x1010` survives, or no fresh return phi exists. |
