# 07 — Post-06 coreutils residue (55/48; the 58/46 bar is NOT met)

**Status:** ready-for-agent
**Depends on:** 06 (staged, uncommitted on `rr-06` @ 3cd0dbf + 4-file
uncommitted delta; DO NOT commit 06 on this score — see below)
**Source run:** `/home/tovpr/scratch-tmp/rr06/cu-pipe/` (lift 103/103,
test, summary stages, full pipeline, 2026-09-04 night)

**Provenance (verified by the tail worker, not assumed):** the installed
plugin `/home/tovpr/.opam/bap-flambda/lib/hike/hike.cmxs` (md5
`b69902d8…`) is byte-identical to the `rr-06` tree build
(`/home/tovpr/scratch-tmp/rr06/build/default/src/hike.cmxs`) — the lift
genuinely ran the staged fix. Unit suite on the tree: 450 ok / 0 FAIL,
`ALL CBAT TESTS PASSED` (rc=0), atexit pins H0/H1/H2/V0/H3 green.

**What 06 fixed (machine-proven):** `__cxa_atexit(i64 undef, …)` went
75/108 (ticket claim) → **0/103** (every lifted IR carries a non-undef,
non-poison handler arg); exemplar `cat` PASSES. The RDI-drop mechanism
is closed.

**Score: 55 PASS / 48 FAIL — below the ≥58/46 acceptance bar, so 06
stays uncommitted.** Residue (48), classified by the tail worker:

- **A. malloc-PLT-stub self-recursion (6: dir, dircolors, ls, sort,
  vdir, wc).** The lifted IR contains `define @malloc` (full SysV
  params — the stub did NOT shrink) whose body calls `@malloc`, which
  interposes to itself → infinite recursion in `setlocale` → SIGSEGV
  with zero output (gdb-proven on ls/wc). Same PLT-stub-boundary
  family as 06, DIFFERENT mechanism (stub over-preserved, not
  value-dropped). Needs its own lane: a lifted `malloc` that tail-calls
  `malloc` must bind the callee to libc, never to itself.
- **B. full-output-then-crash at exit (3: nl, split, uniq).** Byte-
  identical stdout, then SIGSEGV in lifted code on the exit path
  (gdb-proven on nl: crash in lifted frames below `__libc_start_main`
  return). The atexit call shape is textually identical to passing
  `cat` (`@__cxa_atexit(i64 %4, …)`) — so `%4` is a wrong-but-non-undef
  handler. Same value-loss class as 06 through a different escape;
  prime suspect for the next fix after 06 lands.
- **C. startup/early crashes, unclassified (24: b2sum, chmod, chown,
  cksum, date, dirname, env, groups, join, logname, pathchk, pinky,
  realpath, rmdir, seq, shred, split? no — see B, sum, timeout,
  touch, unlink, users, whoami, who, yes).** Zero/partial output.
  NOT one shape: b2sum = indirect call through NULL (0x0) early in
  main; date/touch/sum/users/realpath crash at distinct nonzero PCs;
  pinky dies inside a shared mapping. Full list with crash PCs in the
  tail report; each needs per-binary gdb triage.
- **D. same-rc output diffs (8: cp 1v1, dd 0v0, du 0v1, id 0v0,
  `[` 2v2, mkfifo 1v0, ptx 0v1, truncate 1v1).** Ticket 06 named
  cp/dd/du; id/`[`/mkfifo/ptx/truncate are extra. No analysis done.
- **E. lifted-side aborts rc=134 (3: df, printenv, stty).** Ticket 06
  named all three; untouched by the staged fix.
- **F. link failures (4: getlimits, numfmt, od, tail).** Pre-existing
  per ticket 06 — mechanism spot-confirmed on getlimits:
  `undefined reference to intrinsic:fconvert_rne_ieee754_binary_32`
  (emitter references an FP-intrinsic it never defines; long-double
  code, the x87-gap family). Reproducible without any VSA involvement
  (bil2llvm.ml untouched by 06), so the pre-existing claim stands.

**Suggested order:** land 06 as-is (its marker is at zero; A–E are all
still present WITHOUT the fix's signature, i.e. none is caused by it),
then B (same class, smallest delta), then A (one rule, 6 binaries),
then C/D/E per-binary.
