# 03 — the typed frame model (prototype)

DONE 2026-09-09 (prototype milestone). The owner's directive: change the
stack model IN THE GENERATED CODE so the conversion is simpler and the
result more optimizable — the endgame's "fallback → goal" flip
(AGENTS.md principle 7).

## The model (settled by grilling)

- ONE typed byte-array alloca per sub; every frame-proven access emits
  as **typed GEP + load/store** — no inttoptr, no anchor ptrtoint in the
  access path. All cells share storage, so the model is sound by
  construction; per-access splitting is delegated to LLVM's SROA and is
  MEASURED, not pre-computed.
- **inttoptr/ptrtoint survive only as the documented exception lane**
  (section/global constants, whose addresses are not frame-relative).
- Implementation insight that made it small: the model's fake addresses
  are already byte offsets — the emitter routes the address integer
  through the frame base (`gep frame, (addr − anchor + anchor_idx)`) at
  the single choke point `create_inttoptr`. No per-access tag logic.
- Selection: the BAP pass parameter `--hike-stack-model=typed` (the
  sanctioned control channel). Default model byte-identical to the L1
  reference (verified).

## Acceptance (met)

3/3 semantics PASS (native-vs-lifted stdout byte-identical: factorial,
byte_copy, fizzbuzz_safe) and the opt report
(`scripts/semantic/opt_report.sh`):

| binary | model | pre insns | pre i2p/pt | post-opt insns | post i2p/pt |
|---|---|---|---|---|---|
| factorial | cur = typ | 261 | 7 | 59 | 6 |
| byte_copy | cur | 334 | 13 | 196 | 21 |
| byte_copy | **typ** | 348 | **6** | **170** | **6** |
| fizzbuzz_safe | cur = typ | 918 | 4 | 101 | 2 |

byte_copy — the escape-class binary — is the proof: −13% post-opt
instructions, −70% address-int conversions. factorial/fizzbuzz_safe are
precise (regions) and identical under both models, as expected.

## Notes

- The default model is untouched: `--hike-stack-model` defaults to
  `offset`; the typed branch is gated on `typed_stack`.
- The exception lane partition: constant addresses = section/global
  (inttoptr, correct — they are not frame); non-constant = frame-relative
  (typed GEP, correct — the tags guarantee residency).
- Alignment is LLVM's business on typed accesses (no runtime guards);
  a follow-up may claim align attributes where the VSA proves them.
- Generalization (flip the default corpus-wide + delete the offset
  access path) is a deliberate re-baseline lane, gated on this report
  and the full battery.
