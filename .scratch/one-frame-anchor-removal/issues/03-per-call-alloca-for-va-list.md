# 03: Per-call alloca for va_list / struct-by-value args (caller side)

**What to build:** The current emission for a varargs / struct-by-value
call has the caller push the call's data into its own frame at
anchor-relative offsets and pass a `hike_stack` (RSP) pointer to the
callee; the callee reads via inttoptr arithmetic with offsets that
don't agree across caller/callee (the root cause of `out_va_arg_vacopy`'s
`second pass: ... 1977392` vs native `1 2 3 4 5 6`). The fix routes
the call's data through a per-call alloca: the caller allocates a
fresh `[N x i8]` alloca, initializes it with the call's data (the
va_list struct fields, or the by-value struct copy), and passes the
alloca's address as the `hike_stack` argument. The callee reads/writes
via a stable pointer (the alloca's address), no inttoptr arithmetic
with anchor-relative offsets.

**Blocked by:** T02 (VSA value-tracking). The per-call alloca's size
needs the callee's `info.Convutils.offsets` (the span of all accesses
the callee makes via the `hike_stack` arg); the VSA must classify
those accesses correctly first. T02 makes this classification
possible.

**Status:** ready-for-agent (after T02 lands).

- [ ] A new `Convutils.vla_bounds`-style field in `Convutils.vsa_info`:
  `callee_arg_area_size : int64` — the span of all `hike_stack`-relative
  accesses the callee makes. Computed by the VSA from the offset
  range of the relevant defs whose `addr` involves the
  `hike_stack_var`.
- [ ] `create_func_call` allocates the per-call alloca when the callee's
  `info.callee_arg_area_size > 0`. The alloca is sized to
  `callee_arg_area_size`, initialized with the call's data, and its
  address is passed as the `hike_stack` arg.
- [ ] The caller's existing inttoptr-based pushes (the 8-byte retaddr
  slot, the varint spills) are routed THROUGH the new alloca instead
  of through the caller's frame.
- [ ] `dune runtest` green; no regressions.
- [ ] `run_corpus.sh` 31/31 rc=0.
- [ ] `check_allocas.sh` 124/0.
- [ ] `run_semantic_all.sh` — `out_va_arg_vacopy` either PASSes or
  moves closer to PASS; `out_variadic` may also benefit if the
  per-call alloca removes a class of inttoptr-misalignment bugs.
- [ ] `AGENTS.md` §Current validation state updated.

**Notes:** This ticket is a focused change to `bil2llvm.ml`'s
`create_func_call` and `create_call_args`. The VSA's new
`callee_arg_area_size` field is the only contract change; the
emitter reads it. No semantic change to the call's return value
or argument registers.
