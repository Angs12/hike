# Pins — test_integration

Module: `test/unit/test_integration.ml` (group `integration`, ids
`INT-01`…`INT-23`; `INT-11`/`INT-12` were never minted — the source
sweep skipped them — and the survivors' id gaps carry no meaning),
merging the word-domain / backward-walk soundness properties and the
landmark / T5 pins from `test_cbat/test_properties.ml` and
`test_cbat/test_landmarks.ml`. Every source `check` site is carried as one
assertion inside the pin named for its property; none retired. The three
loop properties (R10b, R5, W1) run their whole sweep inside one pin with
their counters local. Each pin builds its own fixture; nothing crosses pins.

The mechanisms below are not Test_seam-switchable (no disable flag exists),
so — per the lane spec §Fail-before — the disable recipes are textual and
name the production site to break; the recorded red is the state that recipe
produces, re-demonstrated whenever the cited mechanism changes. Production
`src/` is never modified.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| INT-01 | `Clp.logand` (`cbat_clp_core.ml`) and the composite `WordSet.logand` (`cbat_clp_set_composite.ml`) over-approximate the elementwise AND at widths 8/16/32/64 and under mixed-width zero-extension. | In `cbat_clp_core.ml`, make `logand` return `Clp.intersection`'s hull or `bottom` (drop the exact width-wise product). | `bad_clp > 0` (a witness `x&y` is excluded); the composite check follows if the lift is broken too. |
| INT-02 | `Clp.intersection` of two step-1 arcs equals the modular reference at width w+1 (empty / exact arc / smaller-operand two-piece). | In `cbat_clp_core.ml`, return the wider operand for a wrapped pair instead of the exact arc/hull. | `bad` is nonempty: a structured or random pair reports the wrong meet. |
| INT-03 | `Clp.of_list` contains every iterated element (universal) and is exact on a full residue class; it is sound on arbitrary lists. | In `cbat_clp_core.ml`, drop an input element (or return `bottom`) in `of_list`. | `cont_failures > 0` / `arb_failures > 0`, or a full-class case raises the `failwith` stop. |
| INT-04 | `Cbat_backward.inverse_denote` seeds the guard pre-image; the diamond's entry range refines the taken/fallthrough edges to absolute halves. | In `cbat_backward.ml`, make the guard inverse the identity (return `env` unchanged). | VSK-MIXED-SEED/TAKEN/FALL fail: `x` stays `[0,20]` or the seed set is absent. |
| INT-05 | `Clp.widen_join` is above both operands (never lands short of the join). | In `cbat_clp_core.ml`, make `widen_join` return its first argument. | `Clp.subset p2 r` is false (checks 1, 2, 4). |
| INT-06 | Landmark acquisition is scoped to the enclosing WTO cycle (`cbat_landmarks.ml` `widening_at_head` / `observe_unsat_var`). | Make `observe_unsat_var` a no-op, or scope the landmark table process-wide (`clear_head` a no-op). | Loop 2's head lower bound drifts off `K1+1`; loop 1's off the entry constant 0. |
| INT-07 | `Cbat_backward` accumulates the edge condition (`constrain_edge` + the accumulated negatives), partitioning the when-chain. | Use only the jump's own cond (drop the accumulated negatives in the backward walk). | T01-1b/1c read the full seed set `{5,15}` / `{5,15,25}` instead of the singletons. |
| INT-08 | The deep walk's cell meet keys by the same-iteration address denotation (T5-1: the load after the store meets `{5}`). | In `cbat_backward.ml`, denotate the load's address on the block-entry state instead of the same-iteration address. | The cell stays on the wide `[0,200]` range (or top), not `{5}`. |
| INT-09 | The Store row flows a cell constraint into the stored data's producers (T5-2: load KA → copy → store KB → load KB). | In `cbat_backward.ml`, drop the Store row from the def-constraint walk. | The producing load's cell (KA) stays wide, not `{6}`. |
| INT-10 | `Hike.Sections.dynamic_alloc_tids_of` re-checks the seed table against the final denotations: a bounded literal SP decrement is not a VLA event, an unbounded runtime size is. | Classify by shape (any `RSP` decrement) or require a literal size. | The bounded fixture gains an event, or the unbounded fixture loses one. |
| INT-20 | The contrast baseline: a plain `AI.widen_join` drives a cycle-written cell's data infinite (`cbat_ai_representation.ml`). | Make the plain memory widen stop widening (return an operand). | `Ws.is_infinite (cell_of plain)` is false; the contrast collapses. |
| INT-21 | `AI.selective_widen_extrapolate` self-gates each cell on its OWN landmark entries: no own entries ⇒ plain widen (no borrowing of the word lane's entries). | Have the memory arm translate a cell that has no own entries. | `cell_of r <> cell_of plain`. |
| INT-22 | A cell with its own entry translates by that entry's steps (`record_landmark_for_cell` / `entries_for_cell`; `dist_p` growth 2 × 1 step: hi 2 → 4). | Drop the cell arm's Finite translate (or the per-cell row lookup). | `Ws.max_elem (cell_of rl) <> 4`. |
| INT-23 | A bottom old cell state stays the plain widen (the bottom guard in the cell arm). | Let the bottom old state extrapolate instead of widening. | `cell_of r_ex <> cell_of r_w`. |
| INT-13 | Landmark-directed widening over the jle counter (F1): the head and taken view keep the entry constant 0 as their lower bound. | In `Vsa.init_sol` / the entry transfer, seed the counter from top instead of the entry constant. | `Ws.min_elem` is no longer `0` (or is absent). |
| INT-15 | The fallthrough-edge fixture (F1-FT): head `[0,K]`, taken body `[0,K-1]`, fallthrough exit `{K}`. | Make `lm_calc_steps` always `Inf` (plain widen at the head). | Head max ≠ K and the exit is not the singleton `{K}`. |
| INT-24 | The landmark consumption fires: one reading warms an entry (`Zero`), a second, closer reading yields the traversal-step estimate (`Finite`; `cbat_landmarks.ml` `steps_of_entries`). | In `steps_of_entries`, never return `Finite` (always `Inf`). | The second `lm_calc_steps` is not `Finite 1`. |
| INT-25 | A landmark entry consumed without a fresh reading carries nothing: it must not hold the head in the non-widening `Zero` arm while a live sibling entry has steps. | In `steps_of_entries`, let any entry with `dist_p = None` force `Zero` (drop the `fresh` filter). | The live entry's `Finite 4` reads `Zero`. |
| INT-28 | The rotation keeps an entry's history: `lm_advance`/`advance_cell` rotate the reading an entry holds, and an entry with no fresh reading keeps the previous one (`cbat_landmarks.ml` `rotate`). | Overwrite `dist_p` with `None` on every advance. | The reading after an empty round reads `Zero`, not `Finite 1`. |
| INT-26 | Landmark acquisition requires both values on the same coordinate line: a stack-symbolic value against a plain word is disjoint by line, not a disabled behavior (`observe_unsat_var`). | Drop the `same_line` guard in `observe_unsat_var`. | A landmark is recorded for the cross-line pair. |
| INT-27 | The landmark distance is the counter's own signed walk: `-99999` to `0` measures 99999, not `2^64 - 99999` (`distance_words`). | In `distance_words`, read the difference unsigned (`to_int_exn`/`to_int64` without the sign-aware magnitude). | The recorded distance is the `2^40` cap. |
| INT-19 | The walk's cell meet through a Load-producing def (F1-B4): the walk moves the cell off its wide stored range. | In `cbat_backward.ml`, have `constrain_cell_on_trace` fabricate a value outside the stored range. | `Ws.precedes full_cell wide` is false (the cell leaves the wide hull). |
