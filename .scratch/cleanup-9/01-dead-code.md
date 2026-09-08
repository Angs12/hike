# Ticket 01 — dead code (the zero-risk batch, first)

Deps: none. One battery-verified commit. IR byte-identity 32/32 expected
(not reachable from any pass, except where noted).

Delete (each verified zero-caller or provably dead this session):
- The `Cbat_word_ops` **`lt_int`** (its `gt_int` sibling has live users) and
  the substrate's `of_int32` (the full twin fold is ticket 02 — this only
  takes the two dead exports).
- `jmp_target` in the VSA engine (zero callers).
- `Convutils.kind_lo` (zero callers; `is_positive_kind` won).
- `canonize`/`canonize'` in the map lattice (identity no-ops, zero callers).
- The identity `List.map ~f:(fun x -> x)` binding in the extraction walk.
- ~70 lines of blank/banner debris (six sites of 10-20 blank lines each
  holding orphaned banner comments) in the VSA engine file.
- `src/jmps.smt2` (dead SMT sketch, zero refs, `git rm`).
- `src/package.json` + `package-lock.json` (npm tool residue; `node_modules/`
  already ignored) — flag to the owner before the git rm if unsure.
- The orphaned probe `defsize.ml` (unbuildable — no stanza) and the dead
  half of `census.ml` (the state-walk path is never called; its always-empty
  output blocks die with it).
- `StrMap` + `let requires = []` in the pipeline file (zero uses; the
  extension loader reads no such value).
- The four unused module aliases in the VSA pass file.
- The eight orphaned ABI exports (resolve_alias, theory_regs, base_regs,
  is_preserved, is_sp_t, is_fp_t, is_sp_or_fp_t, callee_saved) — the
  callee-saved *predicate* form with one live consumer STAYS.
- The tautological tag guard + its unreachable `failwith` arm in the emitter
  (the guard tests the value the match already bound; the invariant arm is
  unreachable by construction) — and thread the already-found tag into the
  memory-access dispatcher instead of the second lookup.
- AGENTS.md's ghost `docs/vsa-usage.md` staleness bullet (the file is gone).

Acceptance: full battery green; suite output byte-identical (no check
names/counts touched); byte-identity for the two emitter edits.
