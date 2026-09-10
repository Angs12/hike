# T15 — the single representation: tags carry the denotation; relativize_opt dies (P2)

Owner directive (2026-09-11): "Why use relativize_opt???" — asked after
T14 exposed its smear arm as the escape-bug's carrier.
Spec: `.scratch/typed-model/spec.md` (binding constraints apply).
Blocked-by: **T14** (the surgical correctness fix lands first; this
lane then absorbs its accessor) and **T10** (extract/classify in
flight). Blocks: nothing; simplifies T5/T9's input.

## Why the bridge exists (recorded before it dies)

T3's coordinated flip was de-risked by keeping downstream identical:
the word domain gained the absolute segment symbol, the TAG product
kept the old entry-RSP-relative offsets, and `relativize_opt` bridged
them (denotation − base → relative offsets; Option = "stack-symbolic
at all?"). The flip landed; the bridge stayed — and became two
representations of one fact, with the code relativizing TWICE (at
classification, and again at materialization: `val − anchor +
anchor_idx`). Its smear arm (the plain-band re-tag) leaked into the
escape question and produced the T14 bug: callers cannot tell "the
proof" (StackOff) from "the smear" (the band) — the contract blurs
them.

## What lands

1. **The tag product carries the DENOTATION** — the segment WordSet,
   absolute. `classify` reads the denotation's shape directly
   (in-segment / TOP / bottom). The partition's overlap math is
   representation-agnostic (absolute intervals work identically).
2. **`relativize_opt` is deleted**, with its Option and its smear arm
   — T14's `stack_offsets` accessor becomes a trivial domain match
   (the escape-extent rule keeps its semantics: only StackOff).
3. **ONE relativization remains**: the emitter's anchor subtraction at
   materialization (already the GEP's `val − anchor + anchor_idx`).
4. **The geometry recomputes from absolute extents** (frame_dims/
   window_dims subtract the anchor — the same arithmetic, one
   representation earlier... verify where it lands cleanest).
5. **The pins modernize deliberately**: tag VALUES become absolute —
   every fixture/pin re-derived with verification (the T8 precedent;
   the big-ticket item of this lane).

## Sequencing note

T14 lands first (surgical; restores spill_many; the invariant "only
StackOff sizes the frame"). T15 then makes that invariant structural —
the accessor T14 introduces dissolves into a direct domain match.

## Battery protocol (you hold the shared plugin slot)

Same as T1's (see `T1-opt-safety-regression.md` §Battery protocol):
`eval $(opam env)` first; `record_provenance.sh` after every install;
battery artifacts on home disk (`/home/tovpr/tm-battery/t15/`). Gates:
`dune runtest` (the FULLY GREEN suite stays green — fixtures re-derived
with verification), emission rc=0 both lanes, check_allocas, strict
-O0 semantics ALL PASS, strict opt-safety ALL PASS or inventoried, the
pinned gate (attribution-only movement), convergence rows vs the
pre-T15 reference.

## Acceptance

- Grep-clean: `relativize_opt` gone; the tags carry the denotation
  (the type is the proof); exactly ONE relativization site remains
  (the emitter's anchor subtraction).
- All gates green or inventoried; the pin at 7 (or its attributed
  shrink); spill_many's fix semantics preserved.
- Verdict: the new representation, the deleted bridge + smear arm,
  the pins' re-derivations, the gate table, the pin movement, the
  convergence rows.

Worktree: `/home/tovpr/hike-t15`, branch `tm/t15-single-representation`.
