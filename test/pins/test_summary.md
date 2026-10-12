# Pins — test_summary

Module `src/hike_summary.ml` (`Hike.Summary`). One row per pin in
`test/unit/test_summary.ml`. Every fixture is solved by the production
fixpoint (`Common.produce`) before `of_solved` reads it.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| SUM-01 | a canonical return comes back; the written set is the sub's own register defs | start the fold with `adds = None` | SUM-01.rcx FAILs (anything written) |
| SUM-02 | a tail call comes back iff the callee's summary does | make `through` return `back = tail` | SUM-02.noreturn FAILs |
| SUM-03 | a call joins the callee's written set; an unknown callee writes anything | drop the callee's `written` from `through` | SUM-03.joined or SUM-03.unknown FAILs (review) |
| SUM-04 | an indirect jump with no enumerable case words is unknown | classify an unenumerable target as `internal` | SUM-04 FAILs (review) |
| SUM-05 | a trap writes anything and is not an exit | give `Int` the `pessimistic` contribution | SUM-05 FAILs (review) |
| SUM-06 | only reachable blocks contribute; an exit the solve proved dead does not | filter no blocks | observed FAIL with the filter disabled |
| SUM-07 | a return whose RSP is not entry + word draws the fixed diagnostic; the summary still assumes the ABI restore | drop `check_restore` | SUM-07.diag FAILs (review) |
