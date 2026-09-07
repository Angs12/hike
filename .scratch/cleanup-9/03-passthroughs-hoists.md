# Ticket 03 — pass-throughs + hoists (byte-identity oracle)

Deps: none (lands after 02 for clean diffs). One battery-verified commit.

Pass-through removals:
- The emitter's re-derivations: the positive-kind guard (call the shared
  vocabulary's predicate), the precise-model test (call the stack model's
  predicate), the local Hashtbl alias (the shared one is already open),
  the dead `is_main` disjunct, the unused builder/module params on the
  .text loader and the sub emitter.
- DCE's two one-line aliases (the region-mem test and the return-reg test)
  — inline the single home's name.
- The ABI getter that re-projects the target: body-swap to the context's
  already-carried ABI record (value-identical; the record is filled from
  the same projection at context construction).
- The substrate shims at the frame constants (see the hoist below; the
  constants go substrate-native).
- The fixture module's duplicate opens and the double module alias; the
  mixed qualified/alias spellings inside the regression file (mechanical
  normalize — one file, two names for one module).
- The KB conflict-printer literal re-wrap (the mangled spacing is
  operator-facing).

Hoists (each a named binding at the owner, no behavior change):
- The signature rank's per-var ABI projection inside the sort comparator —
  one ABI record + one rank list at function top. Signature order is
  IR-visible: hoist the inputs only, never the comparison.
- The stack-to-locals per-def ABI resolve out of the address-base helper.
- The indirect-call tid bound once per call block (was interned three times
  in one function); the marker/intrinsic/trap string constants beside
  their owners; the region-alloca name minted by the stack model (the
  emitter stops hand-typing the third fission name string).
- The probe timing helper into the shared probe shell (three identical
  bodies).
- Gate the stages-profile probe to the debug profile (its header already
  says so).

Acceptance: full battery; corpus IR byte-identity 32/32 (this ticket's
whole point is that none of it is reachable in output); suite output
byte-identical.
