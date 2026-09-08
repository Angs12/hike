# Ticket 07 — The -O2 corpus joins the battery permanently

Blocking: 06 (code settled; measurement is honest only against the final tree).
Blocks: 08 (the docs cite measured -O2 numbers).

## Change

`scripts/compile_corpus.sh` grows the -O2 lane: same sources, `-O2
-fno-stack-protector`, PIE-only (the same `file -b | grep 'ELF 64-bit.*pie
executable'` hard-fail), second output directory (`/tmp/corpus-o2` by default —
or a home-disk root per the cleanup-9 `/tmp`-capacity hazard note; the script
should honor an `OUT`-style override for both directories).

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
3. **Tag-kind before/after as MEASUREMENT** (not a gate): run the pre-change
   plugin over the -O2 corpus once BEFORE ticket 01 (with the T1 control
   emission) and record the tag-kind census per binary; after the lane, the
   delta table goes into the lane verdict — the expected direction: fewer
   whole-sub fallbacks (false escapes and by-name unbounded degradations gone),
   never more.
4. **-O0/-O2 semantic agreement** (the battery-merged precedent): the same
   sources' lifted binaries should agree with their natives at both -O0 and
   -O2 independently — a disagreement LOCALIZES the fix (the 2026-09-02
   stale-plugin incident was caught by exactly this differential).

Also: `run_corpus.sh`/`check_allocas.sh`/the semantic scripts take the corpus
directory as a parameter already — verify no -O0-only assumption (the list stub,
setjmp linking, the harness) hardcodes; the -O2 binaries may exercise paths the
-O0 ones don't (setjmp inlining, variadic shapes).

## Gates

- -O2 corpus: 32/32 rc=0 emission; semantic harness PASS (record the honest
  per-binary table; knowns recorded, not exempted); check_allocas with the
  failure classes classified; opt gate over the -O2 IR.
- -O0 gates rerun at the tip (the lane's standing gates).
- The measurement table (tag census before/after) lands in the lane verdict
  (`.scratch/sp-only-stack-semantics/verdict.md`).
