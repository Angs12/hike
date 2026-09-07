# VH-00 — Experiment zero: force floors, dump the plan

**Status:** in-progress (worktree /home/tovpr/backup/wt-vh00)
**Depends on:** none
**Blocks:** VH-01, VH-02, VH-03, VH-04

**What to build:** a throwaway probe (or temporary forced-verdict hook, DELETED before commit — never merged) that fires variable floors on the 7 linearizable dynamic defs in `alloca_vla` main and dumps the region plan verdict-off vs verdict-forced (dump_tags ALL-sub mode over a fresh corpus rebuild). Decision output: does `buf`-above-both isolate (ladder confirmed), or does a fifth rule surface (it becomes the new ticket zero and the ladder re-grills)?

**Done when:** the committed diff is docs-only (experiment record in the ticket + validation state) OR a fifth-rule ticket exists; either way the verdict-forcing hook is gone from the tree and the suite is green.
