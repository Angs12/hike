# Pins — test_worklist

Module `src/hike_worklist.ml` (`Hike.Worklist`), callee-first discovery
(ADR 0027, T25 steps 4–5). One row per pin in `test/unit/test_worklist.ml`.
The fixtures are `Harness.with_binary` ELFs (code at 0x400078, the image
entry); each pin runs `Hike.Worklist.run` and reads the program.

| id | mechanism | disable recipe | red evidence |
|---|---|---|---|
| WL-01 | `walk` solves a call's destinations before following its fallthrough and keeps the fallthrough only when one may return; `trim` cuts it | `keep_fall` always true in `body` | WL-01 FAILs: the entry keeps its `ret` block (2026-10-12) |
| WL-02 | a cycle head re-solves its members from their tentative summaries until every tentative read is current (`current`), so a base case's return reaches every member | publish without the `current` check | WL-02.f FAILs: the optimistic "never returns" is published and f's call to g loses its continuation (2026-10-12) |
| WL-03 | `claim`: a block holding a term another function owns is copied with fresh tids, so two functions reaching one block keep distinct block, def and jmp tids | `foreign` always false | WL-03.both and WL-03.unique FAIL (2026-10-12) |
| WL-04 | `main_of`: main is the one address every entry call names in the first integer argument; different addresses give no main and the fixed diagnostic | take the first named address | WL-04.agreed/.entry/.diag/.none FAIL (2026-10-12) |
| WL-05 | `link` names every direct call's callee, so a recursive call to the function's own entry targets the sub, not its entry block | keep a call to an own block | WL-05 FAILs; on the corpus the call links to an undefined block-named symbol (deep_recursion, rec_struct, setjmp_longjmp, 2026-10-12) |
| WL-06 | discovery keeps both arms of a conditional (ported from DRIVE-02) | — (structural) | review |
| WL-07 | `learn_dests`: a resolved indirect jump's destination becomes a decode fact on the instruction, so the re-explored body holds it as a block, not a new function (ported from DRIVE-03) | `learn_dests` never reports new destinations | WL-07.no-function FAILs: the target is rooted as a function by the value harvest (2026-10-13) |
| WL-08 | a resolved indirect call's destination becomes its own function (ported from DRIVE-04) | disable both `learn_dests` and `code_words` | review: either lane alone keeps it green |
