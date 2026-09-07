# honest-gate — the unit suite must say what it means

Branch: `honest-gate` (stacked on `emit-seam` @ d5a7404).
Grilling-settled 2026-09-07 (13 questions, Q21–Q33).

## The problem (measured)

`test_cbat/test_common.ml`'s `check` short-circuits on a 22-entry
`ignored_substrings` list: 38 check sites print `ok: … (stubbed)` and
assert nothing. The un-stub experiment (run 2026-09-07, reverted):

- **22 of the 38 silently PASS** — live pins muted by substring overlap
  (T3-7, T3-8, E6-1, E6-2, the C3 caller-frame pin, the A4c
  neighbor-cell pin, the A4a/A4b OR-mask constants, the C1 slot rewrite,
  the R6/G3 TAKEN/tag checks, the C4a/C4b/R11/A1/A4c controls).
- **16 are genuinely red**, classified by measurement:
  - 3 stale expectations — C2/A2/A3 assert the pre-fission
    per-access-sized degraded frame; `degraded_dims` is now a fixed
    8192-byte floor (`Int64.max n 8192L`, `anchor = n − 8`,
    src/bil2llvm.ml:1962-1970).
  - 1 dead fixture — T3-7b (unassertable: the fallthrough edge has no
    target block).
  - 3 redundant — R6/G3's fallthrough `{9}` pin (byte-duplicate
    fixtures; the behavior is already pinned GREEN by the passing
    F1-NEQ/F1-FT properties).
  - 7 real model work — S-4b, C3-outgoing, C4a, C4b, R11, A1, A4c.
  - 2 real soundness bugs (4 check sites) — `meet` (= `intersection`;
    the R2-1 loose-hull class: disjoint circular intervals return the
    full domain) and `logand` (excludes reachable elementwise ANDs).
    The property blocks print ~472 VIOLATION counterexamples per green
    run.

The predecessor lane (`test-honesty` @ 4ee8498, 87 commits behind,
unmerged) classified several of the 22 as "ticketed known-broken"
against pre-ADR-0003 machinery — that ledger is stale; this spec's
measurements supersede it.

## The decisions (grilling-settled)

1. Un-mute all 22 passing checks → honest `check`s.
2. No xfail mechanism, ever. The substring mute is deleted entirely;
   `check` becomes a plain assert-and-count.
3. C2/A2/A3: **deleted** (stale expectations, no restatement).
   T3-7b: deleted (dead fixture). R6 AND G3 fixtures: **deleted
   entirely** (kills the byte-duplication; F1-FT/F1-NEQ own the
   behavior).
4. The 7 model-work checks (S-4b, C3-outgoing, C4a, C4b, R11, A1,
   A4c): **deleted, no record** (user decision; their only future
   evidence is the corpus battery).
5. The 4 soundness checks (meet R5, logand R10b ×3): **un-muted, kept
   red, and the 2 bugs fixed in this lane** — the gate ends green.
6. No VIOLATION tripwire — the checks fail through the normal counter.
7. Sequencing: test-arch commit first (lands with the small,
   attributable red gate = exactly the 4 soundness checks), then one
   commit per bug fix.
8. Every src/cbat_vsa change runs the full battery (per AGENTS.md);
   the bug fixes need tag-stability evidence in addition.

## The bar

- `dune runtest` ends green with ZERO muted checks and no mute
  machinery in the tree.
- IR byte-identity 32/32 vs the pre-lane control for the test-arch
  commit (it touches no production semantics) AND for each bug fix
  (tag-stability: kind multisets identical on the converged heavy subs;
  any tag movement must be investigated before landing).
- The corpus battery green at every commit.
