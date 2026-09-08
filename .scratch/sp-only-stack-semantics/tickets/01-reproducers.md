# Ticket 01 — Reproducers land RED: the heap-RBP model fallout + the -O2 emission class

Blocking: none (lane entry). Blocks: 02, 04, 05.

## Change

Reproducer-first per repo doctrine: pin TODAY'S wrong behavior with fixtures that
assert the POST-fix truth, so they land RED and flip green at T4/T5. No production
code changes in this ticket.

**Control emission FIRST**: before anything lands, record the -O0 control with the
current plugin (32-bin corpus, provenance verified, control dir on home disk with
`TMPDIR` set per the cleanup-9 hazard note). This is the byte-identity oracle for the
whole lane.

## Fixtures

1. **Model-level false-escape (RED until T4):** a heap-RBP sub — the
   `mk_gpr_rbp_sub` shape (`RBP := 0x400000`, heap-indexed load/store) EXTENDED with
   a call whose arg setup copies RBP (`RDI := RBP; call`) — asserting
   `Sm.frame_escapes = false` (heap-RBP is not a frame escape — RBP holds a heap
   pointer, not a stack address). Today `sp_escaped` seeds RBP unconditionally →
   true → the fixture is RED.
2. **Model-level unbounded-fallback (RED until T4):** the plain heap-RBP sub with a
   TAGGED rsp access and an UNTAGGED heap-RBP store, asserting
   `Sm.split_plan` does NOT return `[]` (the untagged heap-RBP store must not
   degrade the whole sub by name). Today `has_unbounded_access` fires on the fp name
   → `[]` → RED.
3. **-O2 emission reproducer, fp_anchor (RED until T5):** a hand-built sub that
   READS RBP without defining it (the -O2 GPR-RBP shape; the def reads the caller's
   RBP into an outgoing arg), asserting the emitted IR contains NO invented
   `fp_anchor`-shaped binding for RBP and that the read goes through the undef+warn
   lane (the RBX treatment — `capture_stderr` per the emitter-fixture grammar).
   Today `build_entry_block` binds `fp := anchor−8` unconditionally → RED.
4. **-O2 cast-width reproducer (RED until T5):** a 32-bit store at `[RBP ± w]`
   where RBP holds a non-stack value feeding a sitofp cast, asserting the cast
   source width is NOT derived from the RBP-name spill rule. (Lands in
   test_bil2llvm.ml where the FP-table wing lives; today the name test fires →
   RED.)
5. **Green pins (already passing — guard against collateral):** the value-true
   twins — a prologue sub (`RBP := RSP` then `[RBP−0x30]`) asserting the Range tag
   and directness (P21-1 already covers the tag; add the model-level assertion:
   `frame_escapes = false`, non-empty split_plan, directness via the base_const
   route once T3/T4 land — this half stays RED until then and is EXPECTED to).

## Gates

Unit suite: new count with fixtures 1–4 RED (the honest gate — they must visibly
fail), 5's green half passing. No battery change (no production code moved).
Control emission recorded + provenance written (`src/record_provenance.sh`).
