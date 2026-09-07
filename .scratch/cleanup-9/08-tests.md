# Ticket 08 — tests + probes (output-byte-diff is the oracle)

Deps: none (can run parallel to 06/07 — disjoint files). One battery-verified
commit. RULE: no check is added, removed, or renamed unless the check-count
change is recorded in AGENTS.md in the same commit (the honest-gate set the
discipline: the suite says what it means).

Fixture consolidation (the fixture-lib lane established the shared
vocabulary — this finishes the job inside it):
- The remaining loop-family builders that still hand-roll the four-block
  scaffolding inside the theme files: fold them onto the shared
  mk-loop/guard vocabulary (exotic shapes stay hand-rolled but on shared
  block/jmp helpers). Verify: the value-exact pins fail loudly if a fixture
  changes — that IS the verification.
- The caller/callee escape-fixture family (four near-copies of the same
  prologue + outgoing-slot shape across the vsa/regression files) → one
  parameterized fixture; the divergent pins stay in their own tests.
- The cell-at-address and bounded-set helper families (same function
  differing by the mem-var name; the bounded ones byte-identical) → one
  parameterized form each.
- The canonical -O0 cmp-emission block (five defs in fixed order — the
  decoder is order-sensitive) written out three times, once already
  factored file-locally → shared, next to the loop builders.
- The shift-semantics families (the pure-CLP block misfiled in the
  backward suite + the overshift/straddle/antipodal families) → one group
  in the domains file with shared operand fixtures; family check names
  preserved.
- The landmark triple-runs (three fixtures of the same loop with overlapping
  pins) → one shared build + one exit-blocks helper; distinct check names
  preserved.
- The run-fixpoint-and-extract idiom (six spellings) → one anchored-run
  helper (defaults: the anchored entry, empty alloc tids).
- The m6/C10/C11 randomized domain properties filed under regression →
  move to the domains file (no BIL, no stack, no seam).

Probe hygiene:
- The two watcher shells (the corpus watcher and the precision probe) share
  ~90 duplicated lines of driver — factor through the shared probe shell
  (workspace allows the cross-dir library link). Output contracts (the PASS
  lines, exit codes) must stay byte-compatible: the scripts grep them.
- The legacy harness entry bypasses the shared shell entirely (its own
  init/sp-of/describe) — wire it on. It also double-sets the address width
  through two aliases of one library.
- The remaining hand-rolled `flat-name` reach-throughs (two sites, one
  probe) — alias once at the shared shell.
- Owner-decision items (do NOT delete unilaterally): the nested-dir edge
  probe and the va_arg pointer probe (both answer closed questions; the
  tickets own the questions). If the owner says delete, delete; otherwise
  pin the replica rule with a comment.

Suite-hygiene riders: the shadowed width-literal helper in the dce tests
(one name, two different word types in sibling files — give the local a
distinct name); the duplicated three component strings in the shift checks
(hoist to lets).

Acceptance: `dune runtest` direct-exe 0-FAIL with the check count recorded
(before/after in the commit message); suite output byte-diffed except the
recorded moves; both probes' output formats byte-compatible with what the
scripts grep.
