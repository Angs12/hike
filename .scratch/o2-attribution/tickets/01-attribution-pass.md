# 01 — the -O2 attribution pass

Bounded: one session, read-only over the pipeline (no src changes). For
EACH of the seven golden-listed binaries produce:

1. **The divergence point** — the construct in `out_<bin>.ll` whose lifted
   execution diverges from native (found from the sem dirs' native/lifted
   stdout pairs, narrowed by IR reading and, where needed, a traced run).
2. **The mechanism class** — named from the spec's priors table, or a new
   class if none fits (new classes are the expected case where the prior
   was -O0-era).
3. **Prior verdict** — confirmed or killed, with evidence (IR excerpt +
   runtime observation).
4. **Fix-lane assignment + size** (S/M/L) and which other binaries the
   fix plausibly carries with it.

Output: this lane's `verdict.md` with the ranked fix-lane order (va_arg
pair presumed first until evidence reorders it) and the red-list accounting
line for the program.
