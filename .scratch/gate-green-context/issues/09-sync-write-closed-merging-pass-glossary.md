# 09: Sync Write-Closed + Merging Pass glossary

**What to build:** The Write-Closed and Merging Pass entries describe the S1 coarser hull and the R12 gate actually enforced by the VSA and emitter.

**Blocked by:** 07: Sync Stack Access + VSA Tag glossary

**Status:** ready-for-agent

- [ ] `Write-Closed` defined as overlap → same hull `[min lo, max hi]`, convertible iff `lo<0 ∧ ¬saves_incoming_reg`, with ABI-visible `k≥0` as per-def skip (not whole-region poison)
- [ ] `Merging Pass` defined as `hike_vsa` `Ws.overlap` hull + `hike_stack_to_locals` maximal overlap components + emitter `region_split_plan` R12 full-coverage gate (zero untagged, inside/disjoint convertible, size-ok)
- [ ] `Avoid` lists no longer ban `partition`/`slot` when referring to `region_split_plan`/`slot_of`
