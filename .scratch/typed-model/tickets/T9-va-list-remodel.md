# T9 — the va_list re-model (P2, NEW 2026-09-10)

Spec: `.scratch/typed-model/spec.md` (binding constraints + the
conversion-first doctrine apply). Emerged from the T4 grilling: the
owner chose "re-model va_list" over a permanent window parameter; the
bridge ships in T4, this lane retires it.
Blocked-by: **T4** (the promotion + the SP Slot must land first — the
re-model consumes promoted parameters).
Blocks: nothing; after T9, NO sub takes a window parameter unless a
mixed unproven remainder demonstrably survives (measured, flagged).

## The measured class

va_arg_mixed (L1: the ud2 poison arm — re-attribute under the new
model first) and va_arg_vacopy (the va_list state round-trip: the
second va_copy'd pass reads a stale 6th element). The T4 bridge gives
variadic subs a caller_window parameter; this lane removes the need.

## The design space (implementer measures both, lands one)

1. **The alloca'd overflow array**: the callee's promoted overflow
   parameters are stored at entry into a private alloca'd array; the
   va_list's overflow pointer targets that array; the walk is
   model-local memory. The va_start/va_arg idioms materialize from the
   promoted parameters (the callee knows the SysV layout: reg-save
   area from the named-register parameters, overflow from the array).
2. **The LLVM-variadic tail**: declare the lifted variadic sub
   LLVM-variadic; the promoted overflow args pass as varargs; the
   va_arg idiom rewrites to LLVM `va_arg`. Deeper emitter
   transformation of the va_arg idiom; only sound where the lifted
   va_arg walk maps 1:1 onto LLVM's lowering.

Whichever lands: NO second mechanism, no window parameter for the
variadic class, complete rules per idiom shape; anything the
denotations/promotions cannot serve is flagged, never hacked.

## Battery protocol (you hold the shared plugin slot in your wave)

Same as T1's (see `T1-opt-safety-regression.md` §Battery protocol):
`eval $(opam env)` first; `record_provenance.sh` after every install;
battery dirs on home disk.

Gates every iteration: `dune runtest` (the 8-failure owner baseline +
named surviving inventory; referee 0 mismatches), emission rc=0 both
lanes, strict -O0 semantics all PASS, check_allocas green, strict
opt-safety all PASS, the pinned -O2 gate — va_arg_mixed/va_arg_vacopy
flipping green is the EXPECTED outcome (proven flips update the golden
list + AGENTS.md in the same commit); a set GROWTH is a REGRESSION and
blocks.

## Acceptance

- All gates green; the variadic subs' signatures carry NO window
  parameter (grep the emissions).
- The convergence rows for the va_arg pair before/after in the
  verdict; the pin movement recorded deliberately.
- The re-model is one mechanism (the doctrine): grep the diff for
  window-threading residues and any new escape-shaped fact.

Worktree: `/home/tovpr/hike-t9`, branch `tm/t9-va-list`.
