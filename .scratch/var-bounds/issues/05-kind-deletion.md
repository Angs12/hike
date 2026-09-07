# VB-05 — Delete the VLA kind (arm removal)

**Status:** done (merged 75e6bcf 2026-09-04; 605 ok / 0 FAIL; zero kind refs outside docs)
**Depends on:** VB-04
**Blocks:** VB-06

**What to build:** with no producer emitting the kind, delete it: the type arm, the vocabulary alias, and every explicit wildcard arm (model visibility, STL cells, emitter fallback, probes) — each deletion must keep the suite green (the arms are unreachable by construction). Any arm whose deletion changes behavior names a producer that still emits the kind — fix the producer, not the arm.

**Done when:** zero `VLA` kind references outside history/docs; suite green; IR-identical to the VB-04 commit except intended conversion deltas.
