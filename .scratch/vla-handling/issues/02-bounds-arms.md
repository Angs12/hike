# VH-02 — Bounds-side arms for the align-up idiom

**Status:** done (merged 425e819 2026-09-04; 640 ok / 0 FAIL; corpus dumps byte-identical — payoff is fixture-level + ordering power pending VH-01)

**What to build:** transfer arms split by side — equality severs (correctly) while bounds carry facts: const-division interval scaling, align-mask `[x−(2^k−1), x]`, same-root/const-side concat folding, shr bound-shifting. Runtime division, true extracts, flag chains stay havoc (pinned). No congruence revival (the F1-NEQ line holds).

**Done when:** per-operator fixtures green (exact arms + havoc pins); align-up sizes upstream of both decrements carry bounds; suite green; payoff counted.
