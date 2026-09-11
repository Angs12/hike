# T5 design notes — the SSE lane def-use mechanism (pre-digest, 2026-09-10)

Read-only exploration on `typed-model-program` @ `2e8f5a2` (pre-T4).
This is the lane's design record; the ticket points here.

## 1. The words-lane def-use path (file:line)

**Forward transfer (the fixpoint's denotation)** — `src/cbat_vsa/cbat_transfer.ml`:
- `denote_exp` **Load** 140–147: address denoted on the current env; `WordSet.splits_by` gate at 144 (step-alignment test, impl `cbat_clp_core.ml:268-280`); pass → `Mem.find` at the address key 145–146; fail → `WordSet.top` (147).
- `denote_exp` **Store** 148–167: top address → whole-memory top (158–160); `splits_by` fail → stored data becomes `WordSet.top sz` (163–164); else `Mem.add` (166–167).
- `denote_def` 206–214 / **`denote_defs` 217–221**: the defs of a block are folded SEQUENTIALLY (phis are identity). This is the only place intra-block def-use is exact.

**Fixpoint driver** — `src/cbat_vsa/cbat_vsa.ml` `static_graph_vsa` 142–402:
- Per-pred transfer `denote_block_with_stores` at 311–315 (applies the pred's whole def fold to the pred's entry state); join 319–322; warmed-head (visits > 10, 269–271) landmark-directed widen 324–349: `lm_calc_steps` → `AI.selective_widen_extrapolate` (336–340), `Zero` → join, `Inf` → plain `AI.widen_join` (344–345).
- Tag extraction `Cbat_extraction.extract` 511–555: a SECOND sequential per-def fold (522–527, `st_before` per def), address tag via `st_tag_of` (533) → `relativize_opt` (536–539) → `classify` (447–461). Addresses are intra-block exact here; tags carry offset spans only — never lane VALUES.
- Widen-cycle var set `need_map` 192–239: vars in def-use SCCs of the cycle — the i256 lane phis qualify (words lane only).

**Deep backward walk (the producer-subtraction lane)** — `src/cbat_vsa/cbat_walk.ml`:
- `edge_constraints` 1270–1478: guard rows; **Load → `Cell` seed 1423–1425**; Store → constraint transfers to the stored value 1476–1478 (shallow seed derivation only).
- `refine_edge_inline` 1595–1667, wired at every conditional jump via `denote_jump` 1670–1772 from `denote_block_with_stores` 1780–1797.
- `refine_edge` 1009–1097: Cell seeds commit through `constrain_cell_on_trace` (1030–1032); contextual backward fixpoint 1038–1072.
- **`reverse_def_walk` 943–980**: the producer subtraction `cstr' = cstr ∩ post_v` (966–968); **`post_v` is denoted against `blk_state = Solution.get sol (tid blk)` — the block-ENTRY state (948–964), documented "loop-invariant over its own defs"**.
- `def_constraints` 843–939: Load arm 848–853; **NO Store arm — a backward constraint through a store def yields `[]` (939)**.
- `constrain_cell` 532–568 / `constrain_cell_on_trace` 676–714: cell meets key by the denoted address in the ENTRY/trace state and commit via `Mem.meet_range` (712) — into the JOINED memory tree, never into a same-iteration store's result.

**Memory domain** — `src/cbat_vsa/cbat_ai_memmap.ml`: keys are address wordsets; values indexed by (width, endian) (64). Point store → `store_merge` overwrite (narrow-into-wide keeps high bits, 324–342); **range store → `join_add` (344–347)** — a loop-varying store address JOINS into the cell. Reads assemble contiguous narrower cells bytewise (`try_assemble_cells` 356–403) or join aligned intersections; gaps → `Val.top` (422). Memory widening `widen_join` 541–557 (per-key data widen).

**Widening** — `src/cbat_vsa/cbat_ai_representation.ml`: `selective_widen_extrapolate` 113–154 extrapolates only `need` WORDS vars (landmark translation 127–142); **memory takes plain `MemEnv.widen_join` unconditionally (line 153)** — landmarks are words-lane-only by documented scope. `WordSet.widen_join`/`extrapolate_steps` at `cbat_clp_set_composite.ml:585/593`.

**Emitter consumer** — the i256 "lane" values are the XMM vars (BAP models them 256-bit). The lift emits a register phi per var per block (`bil2llvm.ml:15–38`, incoming = the pred's last local binding; `undef` at entry) and decomposes SSE lane ops into extract/shl/or trees over i128/i256 (`bil2llvm_exp.ml` Concat 268–276, Load 288–290). Emission is a faithful transcription of BIR; it goes wrong only through the VSA-fed arms: Dead → poison (`bil2llvm_mem.ml:253–263`), the tag-licensed frame routing (`create_def` 266–334, `mem_access` 222–264).

## 2. Iteration-boundary verdict (TODAY)

- **Load after a store in the SAME block: SEEN.** Decided by the sequential fold `denote_defs` (cbat_transfer.ml:217–221), consumed per-pred at cbat_vsa.ml:311–315 and again in the tag fold at cbat_vsa.ml:522–527.
- **Load in a different block of the loop body, or before the store in block order: NOT seen.** It reads the block-entry state = join over predecessors including the back edge (prior iterations), widened at the WTO head. Decided at `process_vertex` (cbat_vsa.ml:285–322) and the head-widen arm (324–349).
- **The backward lane never composes same-iteration defs**: `reverse_def_walk` denotes each def against the block-ENTRY state (cbat_walk.ml:949, 963) — an operand defined earlier in the same block contributes its STALE joined value to `post_v`; cell meets land on the joined memory (`constrain_cell_on_trace`, 676–714); and constraints do not flow backward through stores positionally at all (`def_constraints` has no Store row, 939).
- **Cell-data collapse**: at the fixpoint a loop-indexed store address is a range key; after head-widening the CLP step degrades, `splits_by` fails, and stored data goes TOP (cbat_transfer.ml:163–164) — the vector store loop's data model does not advance, by these two mechanisms (plain memory widen + step loss), not by any gate.

## 3. Per-binary lane-web shapes (-O2, objdump of `/tmp/corpus_o2/*`)

- **union_overlap** — not a vectorized count loop: per-element branch on `m=(5i+1)%3`; the m==2 arm (pc 1140) is the lane web in ONE straight-line block: `mov %al,%ah` (byte dup), `movd`, `pshuflw $0` (broadcast), `paddb %xmm2` (xmm2 = rodata iota `0x0706050403020100`, loaded pre-loop), `movq %xmm0,-0x4(%rsi)` (8-byte store). The recorded wrong cell (u[2] = `0x46D6050403020100`) = the consuming `paddb` reading the STALE loop-carried i256 phi (bits of iteration-0's m==1 double 0.25) where it should meet the same-iteration broadcast/movd defs — the movd/pshuflw are partial writes; untracked bits come from the phi. The `guarded:`/Unbounded diagnostic is the recorded red herring.
- **byte_copy** — init loop `src[i]=(7i+3)&0x7f` vectorized 16 bytes/iter: `paddq` iota vectors + `shufps` + `punpcklwd/hwd` permutation webs + `pand` mask + one 16-byte store per iteration; ~15 loop-carried i256 phis. Lifted IR: hundreds of `or i128/i256` extract/shift/or trees (`/tmp/emit_fresh_o2/out_byte_copy.ll:796–944`), one wide store (census wideSt=1), trunc-to-16 lane extractions feeding the scalar checksum loops. Recorded failure: the web under-stores (1 of 4 chunks) and lane arithmetic consumes stale state.
- **array_local** — two vector STORE loops: b[] loop (pc 1100): lane-iota phi `paddd %xmm3,%xmm1` advancing +16/iter, `pslld/paddd` composition, `movaps %xmm0,-0x10(%rdx)`; buf[] loop (pc 117a): `punpcklwd/hwd` webs + `packuswb` + `paddb` iota, 16-byte store; then separate wide READ loops (`paddd (%rdx),%xmm0`) consuming the stored cells from a LATER loop — the purest store-loop/reader-loop split of the three.

All three have **zero `stack_rN` region splits** at -O2 (verdict census) — their traffic stays on the model frame.

## 4. The array_local convergence gap (~0.18)

First baseline `/tmp/convergence_baseline.txt`: array_local i0/i2 = **131/747** post-opt (ratio ≈ 0.18) — the -O0 lift's scalar store loops fold (131 insns) while the -O2 lift's vector webs survive opt nearly intact (747). Mechanism: the store loops' cells key by the widened address RANGE; per-iteration lane values are constant vectors, but the cross-iteration JOIN + plain memory `widen_join` (no extrapolation, cbat_ai_representation.ml:153) drives cell data to TOP; the reader loops read TOP; no region split fires; opt sees opaque memory traffic. The stall is exactly the "vector store loops must advance" clause: the (loop-index → stored lane value) relationship is never extrapolated into the cell data.

## 5. Minimal-mechanism proposal (doctrine-conformant, one mechanism)

The producer-subtraction discipline extended INTRA-BLOCK, at two precise gaps:

1. **Sequential-state producer subtraction in the deep walk.** Thread the block's sequentially-denoted state (already computable with the pure `denote_defs`) through `reverse_def_walk` so def d's `post_v` is denoted against the state BEFORE d in program order — same-iteration earlier defs included — instead of `blk_state` (cbat_walk.ml:949/963). `cstr' = cstr ∩ post_v` then confines every constraint to values its POSITIONAL same-iteration producer actually emits, and `constrain_cell_on_trace` keys the cell by the same-iteration address. Soundness: the meet only narrows on the trace-exact state; empty intersections drop the live var exactly as today (969–971); the identity (no key / no intersection) stays the answer wherever the address set is unkeyable.
2. **The Store row in `def_constraints`.** A live CELL constraint meeting a same-block store's key takes the pre-image "the stored value satisfies the cell constraint": constrain the store's data exp `u` with the cell's constraint met against the store's own written value (the positional mirror of the existing shallow row at cbat_walk.ml:1476–1478), continuing the walk into u's producers. This is literally "the lane-consuming op meets the lane defs written earlier in the same iteration" over memory words. It reuses the existing `Cell`/`Var` seed vocabulary, the same Live map, the same commit path — no second channel, no gate: where the store's key doesn't intersect, the row is the identity (empty list).
3. **"Vector store loops must advance": extend the selective extrapolation to cell DATA at the head.** At a warmed head, for cells whose key range is written by the cycle's own stores, apply `WordSet.extrapolate_steps ~steps` (landmark translation when entries exist) to the cell data instead of unconditional `MemEnv.widen_join` (cbat_ai_representation.ml:153), with widen_join as the fallback/overflow arm. This is the deliberate scope change from "memory cells carry no landmarks": the recorded scope was documentation, not doctrine — the doctrine (no gates, sound over-approximation, one mechanism) is unaffected. Soundness: `extrapolate_steps` only moves bounds OUTWARD along observed growth with overflow → the ∞ arm (= plain widening); keys never change, so no residency claim is added; the over-approximation may lose precision, never exclude a reachable value.

Deliberately NOT required: any emitter-side change (the emitter is a faithful transcriber; the poison/Dead lane is L1's, already separately recorded), any iteration-boundary gate, any "wait for next iteration" stop.

## 6. T4 / T3c interactions

- **T4 (blocking, landing first)**: promotion changes the measured class — callee incoming stack slots become parameters, so frame traffic these binaries carry shifts; the Caller-window materialization and Mixed select retire; the SP Slot replaces both T3 binding arms and the `sp_restores` edge-keyed mechanism (`bil2llvm.ml:19–24` sits in the phi-update path T5 does not touch, but merges first). T4 also adds four indirect-call corpus sources whose -O2 shapes join T5's measured scope (ticket T5 §"The measured class"). T5's verdict must re-run the convergence table post-T4 — the accounting order is the reason for the blocking edge.
- **T3c (landed)**: the words lane is the sole provenance carrier (the escape is deleted; the partition reads denotations). 21 subs honestly returned to the Frame model — including `union_overlap@member_for` (2 regions lost) — so T5's lane rules must be correct against Frame-model subs (anchor-based frame routing, no region split), not assume `stack_rN` storage. T4's SP Slot anchor is expected to recover that precision, which is why T5 measures after T4.
- **Pin state to plan against**: -O2 golden list = 4 (byte_copy, union_overlap — T5's expected flips; va_arg_mixed — L1 residual; va_arg_vacopy — T9's). fizzbuzz_safe/fptr_table flipped green in T3c and are out of scope.

Key artifacts referenced: `.scratch/o2-attribution/verdict.md` §L3, `.scratch/typed-model/tickets/T5-sse-lane-def-use.md`, T4 ticket, T3c verdict, `/tmp/convergence_baseline.txt`, `/tmp/emit_fresh_o2/out_byte_copy.ll` (stale L1-era IR, lane-web shape still representative). No files were modified; no `dune install`/`bap` run.
