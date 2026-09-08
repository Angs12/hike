# Ticket 07 — The -O2 corpus joins the battery permanently

Blocking: 06 (code settled; measurement is honest only against the final tree).
Blocks: 08 (the docs cite measured -O2 numbers).

## Change

`scripts/compile_corpus.sh` grows the -O2 lane: same sources, `-O2
-fno-stack-protector`, PIE-only (the same `file -b | grep 'ELF 64-bit.*pie
executable'` hard-fail). When OUT does NOT end in `-o2`, it builds `<out>` (-O0)
AND `<out>-o2` (-O2); an OUT ending in `-o2` builds that one lane alone. The
`cd` into `src/progs` is inside the script (not a caller concern).

No emission baseline is snapshotted for -O2 — today's -O2 output carries the
fp_anchor invention, the by-name spill rule, and the whole RBP-as-GPR class this
lane fixes; snapshotting it would pin the bug. The -O2 gates are BEHAVIORAL:

1. **Semantic harness** (`scripts/semantic/run_semantic.sh` +
   `run_semantic_opt.sh`): native-vs-lifted byte-diff over the full -O2 corpus.
   The opt gate is the interesting one: -O2 is precisely the corpus where
   `opt -O2` meets real SROA/mem2reg pressure on genuine SSA-shaped lifted code.
2. **check_allocas** over the -O2 emission (the no-sp-GEP-into-stack_rN and
   1:1-frame asserts; -O2's different tag population will stress the shape
   rules with new shapes — failures classified like the -O0 shape-d class:
   recorded, not silently exempted).
3. **-O0/-O2 semantic agreement** (the battery-merged precedent): the same
   sources' lifted binaries should agree with their natives at both -O0 and
   -O2 independently — a disagreement LOCALIZES the fix.

## Done (uncommitted, this session)

The script is updated (`scripts/compile_corpus.sh`); the lane builds a fresh
`-o2` dir with the same PIE hard-fail. The -O2 corpus worktree reads are in
`/home/tovpr/sp-battery/corpus-test-o2` (the lan-built check dir). The -O2
battery run is recorded in the lane verdict (`verdict.md`, T08).
