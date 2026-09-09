# SP-only stack semantics — lane verdict

Branch: `sp-only-stack-semantics`. This verdict covers the lane through
`28e05c3` (the no-gates deletion) and supersedes the interim numbers in
AGENTS.md's 2026-09-09 entry.

## The lane's arc

1. **ADR 0008** — SP is the only register granted stack semantics by fiat;
   RBP/fp is an ordinary callee-saved GPR (Abi.fp/is_fp/is_stack_reg deleted,
   RBP in callee_saved; fp_anchor invented entry value deleted; the spill
   apparatus deleted — SFLOAT emits sitofp at the operand's own type).
2. **The no-gates ruling (2026-09-09)** — the VSA correctly tags every stack
   access; STL converts without recomputing anything and without gates. The
   whole refusal chain and every per-member recomputation deleted in one cut
   (see commit 28e05c3's message for the full inventory).

## Battery at `28e05c3` (the no-gates deletion)

| gate | result |
|---|---|
| unit suite | **510 ok / 0 FAIL** (was 516: the 6 gate-pinning checks deleted — honest) |
| `dune runtest` (incl. referee) | ALL PASSED; clpequiv **2,861,148 / 0 mismatches** ✅ |
| both profiles build | default + vsa-debug rc=0 ✅ |
| corpus emission -O0 / -O2 | **32/32 rc=0** both ✅ |
| check_allocas (-O0) | **160 passed, 0 failed** ✅ |
| IR identity vs t06-o0 | **0/32** — the deletion legitimately re-codes the corpus |
| semantics -O0 | **10 PASS / 22 FAIL** (was 32/0) ⚠️ |
| semantics -O2 | **18 PASS / 14 FAIL** (was 24/8) ⚠️ |
| optimization-safety (opt-21 -O2 over -O0 IR) | **10 PASS / 22 FAIL** (follows the -O0 cost) ⚠️ |
| instrumentation blocker | clean ✅ |

## The cost, attributed (the owner's decision)

**The 22 -O0 failures are ONE class, not 22 bugs: the measured escape cost,
arrived en masse.** At -O0 nearly every `main` passes a frame-derived pointer
to a callee (`&x` to factorial, bufs to printf-class callees). With the escape
veto deleted, `main`'s cells convert to `stack_r` allocas while the callee
reads the same physical cell at `[RSP + k ≥ 0]` through its own real-stack
lane — split storage, the write-closed violation class. Machine-proven on
factorial: `main`'s `%hike_stack` sp becomes `undef` (the sp-lane def was
deemed erasable by the precise sweep), the pushed-arg cell lands in an alloca
the callee never reads → SIGSEGV (rc=139). This is NOT a tag bug; it is the
falsification recorded in ADR 0008 arriving at full breadth: **the callee's
access through an escaped frame pointer is untaggable in principle** (the
pointer is TOP in the callee's sub), so the tag cannot carry the fact — only
the caller can, and the caller's only channel is refusing to convert those
cells.

The 14 -O2 failures carry the same class plus the pre-existing 8-binary
-O2 known set; 18 PASS (up from 24/8's PASS count only because the failing
set shifted).

## The owner's options (recorded, not decided)

1. **Accept the cost** — the deletion stands; the corpus documents the
   escape class as known-unconverted (precision loss on the caller side,
   never unsound emission of the callee side).
2. **Producer-side repair (the sanctioned fix)** — the escape fact becomes a
   VSA-produced record field (hike_vsa computes it once; STL reads it and
   never recomputes): the invariant holds (one producer, tags are complete,
   the record carries the aliasing fact), and the 22 binaries recover. This
   is the ADR-0008 "producer-fix later" path the owner chose provisionally
   in Round 1 (Q3: "Delete now, producer-fix later").
3. Restore any STL gate — **not on the table**; it contradicts the ruling.

## Artifacts

`/home/tovpr/sp-battery/{nogates-o0,nogates-o2,sem-ng-o0,sem-ng-o2,semopt-ng-o0}`;
controls `t06-o0` (pre-deletion green), `red3-o0` (T04 reference).
