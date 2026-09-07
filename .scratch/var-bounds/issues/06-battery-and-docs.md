# VB-06 — Full battery, docs, ADR record

**Status:** done (merged 62992e1 2026-09-04; full battery green, zero blocked gates)
**Depends on:** VB-05
**Blocks:** none

**What to build:** the complete validation battery on the final tree (unit suite, corpus 32/32 + IR-identity vs pre-change control, structural asserts, 8/8 harness, both 30/2 semantic gates, `alloca_vla` ≥1 region with identical stdout, `va_arg_mixed` diagnostic-shrink count, coreutils IR-identity); CONTEXT.md glossary updates (variable-bounded Range, kind removal, ordering solver, may-subset merge); ADR recording the Range-generalization (supsersession of the kind design); AGENTS.md validation-state refresh per repo doctrine.

**Done when:** every gate green (or precisely part-documented) and the numbers rewritten with fresh timestamps; branch ready for review.
