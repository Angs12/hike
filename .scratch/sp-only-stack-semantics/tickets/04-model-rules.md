# Ticket 04 — Model rules: SP-seeded escape, base_const directness, tag-driven geometry

Blocking: 03. Blocks: 05 (the base_const consumers in stl land here or at T5 — this
ticket owns the MODEL half; stl's `base_exp_of` change rides with it since stl imports
the model). T1 fixtures 1, 2, 5 flip GREEN here.

## Change (`src/hike_stack_model.ml` + `src/hike_stack_to_locals.ml`)

1. **`sp_escaped`: derived closure re-seeded `{SP}` only** (drop the fp seed —
   `fp_bases`/`sp_base`'s fp half). The var-based closure (EVER-held counts,
   arithmetic-only growth, loads never derived) STAYS — its over-approximation is
   the soundness mechanism (an sp-derived-but-value-unproven register still escapes).
   At -O0 RBP joins via its prologue def `RBP := RSP` (identical closure); at -O2
   heap-RBP never joins (T1 fixture 1 flips green).
2. **`frame_value_def` lhs-exclusion becomes closure-based**: lhs ∉ the derived set
   (computed once per sub, shared with `sp_escaped`). Rationale: the -O0 prologue's
   `RBP := RSP` must NOT count as a frame-value def — otherwise EVERY sub
   frame_addr_alias-escapes (total precision collapse). Post-seed change, RBP is in
   the closure only when sp-derived — prologue-RBP stays excluded at -O0, heap-RBP
   (not in the closure) still counts as a frame-value def if its rhs mentions a
   derived var, correctly.
3. **`is_direct_const_addr` → the `base_const` fact**: drop the `is_sp_or_fp` name
   test entirely; a member is direct iff its `base_const` is `Some _` (the base is
   PROVEN sp-derived with a constant offset). Hand-asm `R12 := RSP` members convert
   now (the by-name rule never could); heap-RBP members → `None` → correctly NOT
   direct (their regions stay memory).
4. **`has_unbounded_access`: drop the untagged arm's syntactic disjuncts entirely**
   (tags strictly only — both sp and fp). A tagged Infinite/Unbounded/VLA access
   still degrades (the fallback arm REMAINS); an untagged access of any name no
   longer does. Accepted risk (ADR 0008): the rsp-term-lost edge — an unproven
   sp-mentioning access sharing a physical cell with a converted member would split
   storage; principle-#2-consistent (the disjunct was a refusal-to-refine gate);
   byte-identity + semantics are the empirical guard. T1 fixture 2 flips green.
5. **`degraded_geometry`: tag-driven extents, sp-driven growth.** Extents: the
   tagged accesses' own offsets/spans (Range/Infinite spans; an Unbounded tag = the
   whole-frame arm as today). An untagged access never counts (it emits through the
   real-address lane, never %frame). Growth: keep the MINUS-on-sp syntactic walk
   (the granted fact; catches rsp-sub prologues and VLAs). DO NOT keep an fp or
   name-based extent walk — sp-only syntactic extents would UNDERsize the -O0
   RBP-tagged frame (unsound).
6. **stl `base_exp_of`**: the `Abi.is_stack_reg` name test → the member's
   `base_const` fact (the fission base replacement consumes the proof). The rewrite
   itself is unchanged.
7. **`fp_of`/`is_sp_or_fp` deleted** (callers all migrated by items 1–6);
   `exp_contains_sp` loses its fp parameter and fp disjunct — its remaining callers
   (`is_stack_mem`, `frame_value_def`'s rhs test, `sp_escaped`'s growth walk) are
   sp-only; where `is_stack_mem` fed `has_unbounded_access`, it is deleted with the
   untagged arm (item 4).
8. **`split_plan`/`regions_of_sub` signatures**: drop the `fp` parameter/`fp_of
   target` plumbing (the model is now sp+facts-driven; `hike_vsa.ml`'s calls
   shrink accordingly).

## Identity expectations

- -O0: the closure is identical (RBP joins via the prologue); directness identical
  on name-covered members (base_const holds exactly where the name test held, PLUS
  the R12-class gain); degraded extents move from the syntactic walk to the tags —
  the numbers should coincide where both computed the same offsets; any delta is
  the named risk to attribute (a tagged access outside the syntactic walk's extent,
  or vice versa).
- The `regions_of_sub`/`frame_escapes`/`split_plan` public shapes change (fp
  parameter removed) — the R12/R-series fixtures in `test_regression.ml` update
  mechanically (drop the `Theory.Target.unknown` fp threading).

## Gates

- `dune runtest` — T1 fixtures 1, 2, 5-green-half GREEN; R-series green; honest
  count recorded.
- -O0 corpus IR byte-identity 32/32 vs the control — attribute deltas ONLY to
  items 4/5 (the accepted risk + the geometry move); anything else = investigate.
- Full battery + probes (idstab, sweepcheck, f67census — the frame_escapes/alias
  callers — build and run).
