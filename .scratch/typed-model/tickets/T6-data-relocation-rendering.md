# T6 — L4: data-section relocation rendering (P3)

Spec: `.scratch/typed-model/spec.md` (binding constraints apply).
Mechanism record: `.scratch/o2-attribution/verdict.md` §L4.
Blocked-by: none (independent region — may run in wave 1).
Blocks: nothing.

## What lands

`fptr_table`: relocated data words (`R_X86_64_RELATIVE` addends) must
render as LIFTED-WORLD addresses, not raw original vaddrs. Today the
emitted data global carries the input binary's vaddr; a call through
the table lands on an address that means nothing in the lifted
executable. The rendering must map the relocated addend through the
same world-mapping the code uses (the section remap / lifted symbol
addresses the emitter already computes for code references).

Scope hints: the data-section/global emission path
(`src/bil2llvm_section.ml`, the section list/remap and copy-relocation
facts `emit_program` receives — see `src/bil2llvm.mli`), wherever data
words are materialized as integer constants. Keep the rule general:
every relocated data word renders through the mapping — not a
fptr_table special case.

## Battery protocol (NO bap in wave 1 — you do not hold the shared slot)

Round 1 (blind): implement + `dune build` + `dune runtest` (both
profiles). NEVER `dune install`, never run `bap`. Deliver the branch
with the mechanism described; the merger validates the battery.

If the merger's battery is red (or the fptr_table flip needs
iteration), the ticket REOPENS with the slot granted: then work as T1
does (`record_provenance.sh` after every install; battery dirs on home
disk).

Gates at merge: `dune runtest`; -O0 emission 33/33 rc=0; strict -O0
semantics 33/33; check_allocas green; strict opt-safety 33/33; -O2
emission rc=0; pinned -O2 gate — fptr_table flipping green is the
EXPECTED outcome: a proven flip updates
`scripts/semantic/o2_known_failures.txt` + AGENTS.md in the same
commit (labeled IMPROVEMENT by the pin; that is the designed
movement).

## Acceptance

- fptr_table's -O2 lift post-opt matches native (the flip), or the
  residual is re-attributed with evidence in the verdict file.
- The rendering rule is general (no per-binary shape tests).
- Verdict file: gate table + the convergence report row for
  fptr_table before/after.

Worktree: `/home/tovpr/hike-t6`, branch `tm/t6-reloc`.
