# Pins — test_ssa_verify

Module: `test/unit/test_ssa_verify.ml` (group `ssa_verify`, ids
`VER-01`…`VER-02`). The property verifier runs only in the `vsa-debug`
profile; it checks SSA dominance and boundary-version invariants.
Production mechanism: `Hike.Ssa` and `Hike.Split_blocks`.

| id | mechanism | disable recipe | red evidence |
|----|-----------|----------------|--------------|
| VER-01 | The post-promotion split is an admissible SSA sub: every sub passes the verifier. | Skip phi rewriting in the post-promotion split. | VER-01 raises: the verifier rejects the split sub. |
| VER-02 | A structural arming result is rejected until the SSA commit. | Commit the `Edit.view` without `update_sub`. | VER-02 FAILs: the bare view passes verification. |
