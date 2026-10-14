# Pins — test_call_effects

Module: `test/unit/test_call_effects.ml` (group `call_effects`, ids
`CE-01`…`CE-15`), merging the `CE1`…`CE10` checks of
`test_cbat/test_forward.ml` (the forward Call_effects family) and the
`C1-1`…`C1-5` checks of `test_cbat/test_vsa.ml`.  Every source `check`
site is carried as one pin; none retired.  Production mechanism:
`src/cbat_vsa/cbat_call_effects.ml` (`Cbat_vsa.Call_effects.transfer` /
`indirect_callee`) with the frame-keep core in
`src/cbat_vsa/cbat_ai_representation.ml` (`AI.call_abstraction_frame`).

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
| CE-03 | `AI.call_abstraction_frame` keeps caller-frame cells at/above the highest possible call-time RSP and drops the cells below it (the call-time RSP is `{0x1000}`). | In `transfer`, bypass the frame keep: `let abs = AI.top in`. | CE-03: `Ws.equal (ce_reads m 0x2000 kept_frame) (Ws.singleton (w64 42))` fails — the kept cell reads TOP (review). |
| CE-04 | The escape set is the denotation of `written_lanes`; the caller frame outside an escape lane's range survives, inside it dies. | In `transfer`, drop the escapes: `let escape = [] in`. | CE-04: `Ws.is_top (ce_reads m 0x2000 escaped)` fails — the rdi-range cell survives (review). |
| CE-05 | A pushed site's SP gains one word (`WordSet.add` of the word-size singleton) — the popped retaddr. | In `transfer`, ignore the push: `if false && site.pushed then …` (or `let pushed = false`). | CE-05: `Ws.elem (w64 0x1008) rsp'` fails — only `0x1000` remains (review). |
| CE-06 | `pushed = false` (a trap) leaves the SP untouched — it pops no retaddr. | In `transfer`, make the push unconditional: `if true then …` (or delete the `site.pushed` guard). | CE-06: `Ws.equal (AI.find_word 64 trap abi.Hike_abi.sp) (Ws.singleton (w64 0x1000))` fails — the SP gains `0x1008` (review). |
| CE-08 | `indirect_callee` denotes the target exp; a singleton word passes `Cbat_word.to_int64` into `lookup`, then `callee`. | In `indirect_callee`, answer `Summary None` for the singleton arm. | CE-08: the `Summary (Some ws)` arm is never taken, so the match falls to `false` (review). |
| CE-09 | A non-singleton (unbounded or multi-word) target denotation resolves to `Summary None`. | In `indirect_callee`, drop the singleton guard: take `WordSet.min_elem ws` and run `lookup`/`callee` for any non-top set. | CE-09: the match returns the named sub's summary, so the pin's fallthrough `false` fires (review). |
| CE-10 | A bounded singleton whose word `lookup` cannot name (foreign address) resolves to `Summary None`. | In `indirect_callee`, fabricate a summary when `lookup` misses: `~default:(Summary (Some Int.Set.empty))`. | CE-10: the match returns an empty summary, so the pin's fallthrough `false` fires (review). |
| CE-12 | Every word not in `preserved` is TOPed by `call_abstraction_frame`. | In `transfer`, skip the abstraction for words: return `env` unchanged (no `call_abstraction_frame`). | CE-12: `Ws.is_top (AI.find_word 64 env' y)` fails — `y` still reads `{7}` (review). |
| CE-13 | A preserved `RSP` (no push) keeps its value-set; the preserved fold is var-identity based, not name based. | In `transfer`, ignore `preserved`: `let preserved = Var.Set.empty in`. | CE-13: `Ws.equal (AI.find_word 64 e' rsp) (Ws.singleton (w64 0x10))` fails — the RSP is TOPed (review). |
| CE-14 | A call with an unbounded RSP keeps no frame: `call_abstraction_frame` falls back to the whole-memory top when the RSP denotation is not a single word. | In `call_abstraction_frame`, drop the RSP-bound guard and run the frame split regardless of `Ws.cardinal rsp`. | CE-14: the stored `{0x11}` at `[0x10]` survives, so `Mem.equal … (Mem.top …)` fails (review). |
| CE-15 | The preserved set is matched by var identity, so a virtual var in `preserved` keeps its value-set. | In `call_abstraction_frame`, restrict the preserved match to non-virtual vars (skip `Var.is_virtual` keys). | CE-15: `Ws.equal (AI.find_word 64 e_v vv) (Ws.singleton (w64 3))` fails — the virtual var is TOPed (review). |
| CE-16 | The frame-keep namespace rule: a plain-top escape cannot name the stack line (a stack address is `Rel`), so it never forces the whole-memory top — the caller's frame survives (`frame_keep` in `src/cbat_vsa/cbat_call_effects.ml` omits non-relative escapes). | In `src/cbat_vsa/cbat_call_effects.ml` `frame_keep`, restore the all-or-nothing escape composition (a `None` range forces top). | CE-16: the frame cells drop (review). |
| CE-17 | A `Rel` escape of bounded extent carves exactly its range; the rest of the frame above the call-time SP survives. | In `src/cbat_vsa/cbat_call_effects.ml` `frame_keep`, drop the escape from the list (or `call_keep`'s `in_escape`). | CE-17: the escape cell survives (review). |
| CE-03/04/07 | The frame-keep boundary is OFFSET-space: `keep_lo` is the SP's segment-relative offset (the space Stack cells key by), not the absolute position — the keep is real now, not a degenerate all-drop. | In `src/cbat_vsa/cbat_call_effects.ml` `frame_keep`, restore the `+ stack_base` in `bound`. | CE-03: the cells at/above the SP drop (review). |

| CE-18 | caller-frame survival requires an SP with a stack-family origin | use raw numeric SP bounds after stack_offsets fails | an originless SP incorrectly keeps caller-frame facts |
| CE-19 | an escape lane holding a stack address or NULL carves the stack address's range (the escapes are each value's `stack_leaves`) | read escapes through `in_stack_segment` again | the escaped cell at `0x2000` survives the call |
