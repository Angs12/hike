# Pins — test_strip_canaries

Module: `test/unit/test_strip_canaries.ml` (group `strip_canaries`, ids `SC-01`…`SC-08`).
Production mechanism: `src/hike_strip_canaries.ml` (`Hike.Strip_canaries.strip_sub`).

There is **no `Test_seam`** for this pass, so no switch can be
flipped from the test tier. Production `src/` is never modified. The disable
recipes below are textual; the recorded red is the state each recipe produces
(by review, re-demonstrated whenever the cited mechanism changes). Every pin
builds its own fixture inside its closure — no cross-pin state.

| id | mechanism | disable recipe | red evidence |
| --- | --- | --- | --- |
| SC-01 | Full four-fact composition, under the boundary guard: the deleted canary read is the fixture ret's flow-last RAX writer and the fixture denotations are top, so no proven replacement exists — `boundary_ok` refuses and the identity stands (the corpus's real denotations materialize; factorial@O0-protector-all is the oracle). | Seed the fixture's tls-read denotation with a real singleton and give the domain the equal-operand subtraction — the composition then deletes (the recorded fixture-gap increment). | `check "SC-01"` fails: the idiom deletes (read/store/reload/subtract gone, the fail block pruned, the equality edge forced true). |
| SC-02 | No-RELOAD identity: the composition needs a chain member whose rhs is a singleton-cell load and whose value reaches the compare (`compare_operand_is_reload_value`, the `reload_tied`/`one_cell` gate). A compare reading the read value directly has no reload, so the pass is the identity. | Relax `reload_tied` to `true` (drop the `if one_cell && reload_tied` conjunction to `if one_cell`), so a compare on the direct read fires. | `check "SC-02"` fails: `has_def stripped subtract` is false (the compare def is deleted). |
| SC-03 | No-fail-edge identity: `reach_fail`/`is_fail_block` require the not-equal successor path to reach a direct call whose name contains `stack_chk_fail`. | `let reach_fail ~ctx ~names = fun _ -> true` so every not-equal edge counts as a fail edge. | `check "SC-03"` fails: `has_block stripped tids.(3)` is false (the ret-targeted fail block is removed). |
| SC-04 | Value tie, not name match, under the boundary guard: the alias store is not the canary store AND the guard refuses the fixture (top denotations) — every idiom def survives. | Replace the tie with a name match. | `check "SC-04"` fails: the alias store/read are eaten. |
| SC-05 | Stored value is the TLS read: a local stored to the same cell is refused even with a decoy TLS read present (the `Bil.Var` + denotation test in `stored_value_is_read_value`). | Drop the `stored_value_is_read_value` filter over `tls_reads` (accept any store on the cell). | `check "SC-05"` fails: `has_def stripped read` is false. |
| SC-16 | `prune`'s orphan rule — one reachability pass from the pre-existing predecessor-free roots (the entry and pre-unreachable blocks) over the surviving edges; the rewrite-orphaned fail block drops, pre-existing unreachable blocks stay (`src/hike_strip_canaries.ml`, `prune`) | seed `roots` with the empty set in `prune` | SC-01/SC-06 red: the fail block survives the strip |
| SC-06 | Multi-check shared cell/fail block, under the boundary guard: both compositions refuse on this fixture (top denotations) — both checks, the shared fail block, and both conditional equality edges survive. | Seed real denotations (the SC-01 increment). | `check "SC-06"` fails: the shared fail block is pruned and the equality edges go unconditional. |
| SC-07 | The guard shape gate: the equality edge continues unconditionally only when the fail edge is the later unconditional fallthrough (or the conditions are complements). Two conditional edges with unrelated conditions keep the canary. | Drop the `eq_is_complement` gate in `comp_of_block`. | `check "SC-07"` fails: the read/reload defs and the fail block are deleted. |
| SC-08 | The fail name is exactly `__stack_chk_fail` (optionally `@`-suffixed), never a user symbol containing the substring. | Restore `Base.String.is_substring n ~substring:"stack_chk_fail"`. | `check "SC-08"` fails: the canary is stripped under `my_stack_chk_fail`. |
