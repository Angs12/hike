# Ticket 03 — re-baseline housekeeping and closure — CLOSED 2026-09-07

Done:
1. Fresh reference emissions: `/tmp/opencode/rm1-ref` (plugin provenance
   verified `src=b8a1ec0a`, tree a5a8d0b) — byte-identical 35/35 to
   `rm1-em2` (the ticket-01 build's emission) across two independent
   installs: the re-armed byte-identity baseline. Recorded in verdict.md.
2. AGENTS.md: validation-state entry added (fresh timestamp, the one-time
   renumbering called out with the re-baseline warning for future sessions).
3. The verdict's CORRECTION note: the shared-opam-plugin hazard (the
   parallel session's mid-lane install) invalidated one reference emission
   attempt and exposed that control-side determinism was never measured —
   both recorded.
4. Commits: 8ac54a6 (rewrite) → 73bc0b1 (A/B verdict) → a5a8d0b (review
   fixes) → this closure. Each green.
