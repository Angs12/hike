# Ticket 03 — ABI full sweep, swap-not-add

Status: landed (2026-09-06).
(0.17 µs/call, ~1 ms/binary) — do not sell it as a perf ticket.

## Problem

`Abi.of_target_opt`/`Abi.sp`/`Abi.fp` (which reach into `Theory.Target` and
allocate a fresh record — `hike_abi.ml:92-119`) are recomputed at leaf
granularity: per def in `hike_dce.ml:19-25` (`is_call_reg` builds the
16-element reg list PER DEF), per exp node in `hike_stack_model.ml:9-21`
(`fp_of` inside `exp_contains_sp`'s every-node visit), per warning in
`bil2llvm.ml:576` (68,670 undef-reads per corpus), per phi-incoming at
`bil2llvm.ml:1655`. The facts are static per binary.

## Rule (settled: swap-not-add)

Replace `~target` with `~abi : Abi.t` (or `~sp`/`~fp : var`) **only where
the callee reads nothing but ABI facts**. Where the callee reads non-ABI
target facts (`Theory.Target.matches`, `Target.reg`, width queries), keep
`~target` — the ABI record caches the ABI projection, it does not replace
the target. The signature itself then shows which facts each function needs.

## Sites

**`emit_ctx` (convutils.ml:33) gains `abi`/`sp`/`fp` fields** — filled once
in `convert_binary` (`hike.ml:556-565`). Consumers:

- `bil2llvm.ml:576` (per undef-read), `:766,782,783` (sp/fp compares),
  `:1063,1096,1097,1655` (the per-phi-incoming one — ~100 vars × 700 blocks
  × 3 incomings per sub), `:1813,1824,1889,1890,1896,1897,1887` (pc/sp/fp),
  `:2007` (per sub), `:2103` (per element of a `Core.Set.filter`).
- `hike_dce.ml`: `dce ~target` → thread `~abi` once at :137;
  `keep`/`is_call_reg`/`is_ret_reg` read the record (kills the per-def
  list append).
- `hike_stack_model.ml`: `fp_of :9`, `is_sp_or_fp :16` (per exp node),
  `is_arg_reg :178` (per def), `is_sp_t :293` (per def), and the
  `exp_contains_sp :492` call chain.
- `hike_stack_to_locals.ml:56-58` (`is_stack_reg (Abi.of_target target)` in
  `base_exp_of`'s per-node `is_sf`).

Approximately 40 call sites, 4 files + `convutils.ml`. Mechanical.

## Non-goals (settled)

- `Sub.to_graph` ×3 in the emitter: SKIPPED (0.058 s/binary = 0.3%).
- No behavior change anywhere; this is signature surgery only.

## Verification

- Full battery + IR byte-identity 35/35 — MUST be byte-identical (the ABI
  record is a pure projection; any byte moving means a semantic slip).
- `dune runtest` including the D0-D5 dce fixtures (they call `dce ~target` —
  the seam change updates them; `Hike.Dce`'s exported signature in
  `hike.mli:20-24` is part of the sweep).
