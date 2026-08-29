# 02: Audit the VSA's Unbounded classification on the 3 failing tests

**What to build:** The three failing tests each carry a `hike: guarded:
Unbounded` warning on a def whose address is DIRECTLY frame-derived:
`mem[RBP - 0xB4, el]:u32` in `variadic`, `mem[RBP - 8, el]:u32` in
`va_arg_vacopy`, `extend:128[RAX]` in `nested_struct`. The VSA's
`rewrite_addr` should turn `RBP - 0xB4` into the offset `-0xB4`
(because RBP is frame-derived with the same offset as RSP). The VSA's
`classify` should then return `Range(-0xB4, -0xB4)`. It returns
`Unbounded` instead, which means the VSA's value-tracking is producing
TOP for the rewritten address.

**This audit is mandatory under the new architecture too.** T05
"drop the anchor — one flat frame per sub" replaces the emission
model with a flat frame (no anchor offset arithmetic, no per-region
split). Under the new model, the VSA's classification is the source
of truth: a concrete `Range(lo, lo)` becomes a direct GEP into the
flat frame; an `Unbounded` becomes an inttoptr fallback. If the VSA
returns `Unbounded` for a def whose address IS directly frame-derived,
the emitter falls back to inttoptr arithmetic, which the new
architecture can route correctly (no anchor offset disagreement),
but the result is still sub-optimal. The audit MUST run, even if
T05 lands, because the VSA bug is a logic bug independent of the
emission model.

The first job is to find where the failure is. The candidates are:

1. `rewrite_addr` returns the address unchanged (the frame at the
   partitioned state does not have RBP as derived).
2. `rewrite_addr` rewrites correctly but `denote_imm_exp` evaluates
   the rewritten constant to TOP (the partitioned state's value
   for the constant is wrong).
3. `denote_imm_exp` succeeds but `val_as_imm` fails (returns
   `Error _` which `offsets_of_sub` interprets as Unbounded).
4. The partitioned state passed to `offsets_of_sub` differs from the
   per-def sequential state — the partitioned state may have lost
   the RBP-derived fact at the merge.

The fix is whatever the audit identifies. Likely one of:

- The partitioned state's frame is not the LUB of per-block-end
  frames (a fixpoint bug).
- `offsets_of_sub` uses `st_before` (the pre-def state) but the
  per-block-end frame has RBP only AFTER `RBP := RSP` fires — so
  the pre-def state in a sub-block that doesn't have `RBP := RSP`
  (e.g., the post-call block) loses the fact. The fix uses the
  per-block-entry state instead, or merges the frame with the
  predecessor's.
- The per-def sequential state is correctly tracked but the
  partitioned state's value-set for the constant is TOP because
  the join with the predecessor lost the singleton.

After the audit, the fix is an additive change to `cbat_vsa` (the
audit's diff) and possibly a small change to `hike_vsa.ml` (the
state-threading in `offsets_of_sub`).

**Blocked by:** None. This is a focused investigation in the
`cbat_vsa` library and the `hike_vsa.ml` per-def state-threading.
The audit must run BEFORE T03–T05 because those tickets depend on
the VSA producing correct classifications.

**Status:** ready-for-agent.

- [ ] Audit complete: a focused instrumentation (e.g., a temporary
  `eprintf` in `cbat_vsa.denote_imm_exp` and `cbat_vsa.rewrite_addr`
  for the three failing test binaries) prints the partitioned
  state, the rewritten address, the `denote_imm_exp` result, and
  the classify result for each Unbounded def. The output identifies
  the root cause from the four candidates.
- [ ] Fix lands in the appropriate file (`cbat_vsa.ml` or
  `hike_vsa.ml`); the three failing tests' Unbounded warnings on
  direct frame-derived addresses are gone.
- [ ] `dune runtest` green; no new failures introduced.
- [ ] `run_corpus.sh` 31/31 rc=0.
- [ ] `check_allocas.sh` 124/0.
- [ ] `run_semantic_all.sh` — `out_variadic`, `out_va_arg_vacopy`,
  `out_nested_struct` all move closer to PASS (the 7th varint in
  variadic reads correctly; the vacopy second pass prints
  consistent values; the struct by-value copy returns the right
  checksum).
- [ ] AGENTS.md §Current validation state updated with the audit
  findings and the new gate numbers.

**Notes:** The earlier ticket draft proposed extending `rewrite_addr`
to follow value-typed addresses (`RAX := mem[RBP-0xC8]; mem[RAX]`).
That extension is still useful (the `nested_struct` failure does have
a Cast-of-Load shape `extend:128[RAX]` which may need it) but is
NOT the primary cause of the three failing tests. The primary cause
is the direct frame-derived class failing to classify. The audit
may surface both.

The fix MUST be a `cbat_vsa` library change (the AI state's
frame-relation or the `denote_imm_exp` evaluation) OR a `hike_vsa.ml`
state-threading change. It MUST NOT be a filter that excludes
direct frame-derived accesses from classification (that would be
a "magic filter" — see `AGENTS.md` §Design principle 2: NO GATES).
