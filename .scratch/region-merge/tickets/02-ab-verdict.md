# Ticket 02 — A/B, determinism, diff review, the ≥2%-or-revert verdict

## A/B (interleaved, same binaries)

Control: main @ c46454a build (worktree `/home/tovpr/backup/cleanup-8` has a
built tree; rebuild + reinstall its plugin to be safe). Candidate: the
ticket-01 build. Two runs each side, interleaved (A,B,A,B), pinned to P-cores
(`taskset -c 0-11`, the perf-profile's own environment note).

- `subtimes` producer wall on {/usr/bin/du, /usr/bin/ls, /usr/bin/grep,
  /usr/bin/sort, /usr/bin/gcc-12} (the census binaries; du's
  `__strftime_internal` and gcc-12's sub count are the region-merge-heaviest).
- The stack_model column is the direct readout; the ≥2% claim is on the
  AFFECTED CLASS (producer wall of those binaries), per the settled bar.
- perf spot-check on one heavy binary (grep or du): confirm `exists_17538` no
  longer appears in the profile and the stack_model share dropped.

## Determinism (re-arms the byte gate)

Two full corpus emissions from the SAME candidate build, different output
dirs; `cmp` every `out_*.ll` pair — byte-identical required. This is the
re-armed baseline discipline: future lanes get "IR byte-identity vs the
region-merge control" back.

## Diff review (one-time renumbering)

Per-binary `diff` of the 35-gate emissions control vs candidate. Every hunk
must be one of:

1. `stack_rN` name changes (`stack_rN`, `stack_rN_mem`, `stack_rN_base`,
   `%stack_rN` comments) — renumbering only;
2. alloca/`getelementptr` declaration order following the id renumbering;
3. nothing else. Any other hunk shape = a semantic slip → investigate before
   proceeding. Commit the summarized diff table (not the raw diffs) under
   `.scratch/region-merge/`.

## Verdict

Record in `.scratch/region-merge/verdict.md`: the A/B table, the determinism
result, the diff-review classes, the perf spot-check, and one of:

- **KEEP** — ≥2% on the affected class, all gates green → ticket 03.
- **REVERT** — under 2% → `git revert` the rewrite, record the non-finding
  (the 5.2% symbol attribution over-promised), close the lane. The battery
  being green does NOT keep the change by itself (the user's bar).
