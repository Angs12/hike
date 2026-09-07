# 07 — Exclude absolute addresses from channel-2 seeding

**Status:** SUPERSEDED 2026-09-04 eve — absorbed into ticket 06 by ruling (hunk-2-only):
ablation diff proved hunk 1 masks (frame-garbage load survives) while hunk 2 roots
(control-identical alone), so the exclusion lands in 06 with its pin + churn
battery, not here. Kept as record; do not implement separately.
**Depends on:** none (independent of 06: that ticket lands the PLT-stub signature
rule with no seeding change; this ticket changes the seeding rule itself)
**Blocks:** nothing (does not block the restriction-removal merge — that unblocks
with 06)

**Origin:** split out of ticket 06 by ruling 2026-09-04 eve. Both hunks fixed the
atexit repro independently and both together matched the pre-02 control
byte-identically; the ruling keeps 06 minimal (signature rule only) and moves the
seeding change here, where its churn can be judged on its own.

**What to build:** absolute-immediate addresses never seed through channel 2
(a bare constant carries no frame intent — the absolute-immediate doctrine; a
denoted `{0x2008}` falling inside the ±64 KiB neighborhood is a guess, not a
proof). This is a principled rule correction, not a gate: SUBSET-only contract
unchanged, no per-def refusal, every def stays denoted.

**Prerequisites inside the ticket (in order):**
1. The absolute-address pin FIRST (Channel-2 research §3.5): a fixture with a
   small-absolute load inside the current neighborhood documenting today's
   (seeding) behavior, then showing the exclusion — plus the vector-build
   absolute negative that must stay unseeded either way.
2. Then the rule change (channel 2 requires a variable in the address chain).
3. Corpus-wide churn adjudication: re-emit + diff the full corpus and judge every
   tag delta (expect Unbounded→fewer-false-seeds direction only); the full gate
   battery plus the coreutils pipeline bar from ticket 06.

Gates:
- [ ] Pin fixture green pre- and post-change (documents then proves).
- [ ] Unit suite 0 FAIL; corpus rc-clean with every emission delta judged
      (warning/tag direction only, no shape changes); structural asserts 0 failed;
      semantic gates at the known-failure floor; probes crash-free.
- [ ] Coreutils pipeline at the ticket-06 bar (no regression vs the 06 tree).
