# Ticket 03 — Extraction: export the per-def `base_const` fact into `vsa_info`

Blocking: 02. Blocks: 04, 05.

## Change

One new per-def fact in `vsa_info` (the `~vla_alloc_tids` record-churn precedent):
for each TAGGED access def, **the address's base var and its constant frame offset** —
the base var's frame term when that term is fconst-only; `None` when the address has
no Var base or the term carries fvars.

- **Producer:** the extraction walk (`Cbat_extraction.extract`, `cbat_vsa.ml`) — it
  holds the per-def state (`st_before`/`st_tag_of`) and already rewrites the address
  via `rewrite_addr` for the tag arithmetic; the base+const is derivable in the same
  walk (the frame map's entry for the address's base var, when the address is
  `[base ± const]`-shaped after the rewrite).
- **Record:** `Convutils.vsa_info` gains the per-def map (Tid → (base var × const)
  option); `mk_vsa_info`/`mk_vsa_info_maps` grow the field; `equal_vsa_info` covers
  it (maps, sorted-tid keys — the hand-written equality discipline).
- **Fixtures:** the ~11 `mk_vsa_info` sites + probes churn; the shared-fixture
  builders in `test_common.ml` get the default (`None`/empty map) so the churn is
  mechanical.

Shape decision to make at implementation time (stay minimal): the field serves
three consumers — `is_direct_const_addr` (T4: "is this member's base sp-derived with
a constant offset"), the fission base binding (`base_exp_of`, T4/T5: "which var is
the base to swap for `stack_rN_base`"), and the spill gate (T5: "is this 32-bit store
frame-resident"). A single `(var × int64) option` per tagged def serves all three;
if the fission binding proves to need the full rewritten address instead, prefer
extending the EXISTING `addr` fact (`f.addr`'s `(addr, _)` pair) rather than a second
address-shaped field — one address fact per def, never two.

## Gates

- `dune runtest` (the honest count moves up: add positive/negative base_const pins —
  prologue-RBP access → `Some (RBP, -8)`; indexed `[RBP + i*4 − 0x70]` → `None`
  (fvars); heap-RBP → `None` (untagged, no entry); hand-asm `R12 := RSP` access →
  `Some (R12, 0)` — the coverage the by-name rule never had).
- -O0 corpus IR byte-identity 32/32 (pure record extension — no consumer changed
  yet; identity MUST hold).
- KB provenance + full battery; `Hike_kb`'s join/conflict domain untouched (new
  field rides the existing map-extension machinery).
