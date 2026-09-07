# T4 — Verification: clpequiv + suite + corpus IR byte-identity

Blocked by: T3
Blocks: T5

## Goal

Prove the swap changed **cost, not behaviour**. The failure mode of a
numeric-substrate bug here is an unsound narrowing (the array_local
class) — silent, never a crash. IR byte-identity is therefore the gate,
not a nicety.

## Gates (all must pass)

| gate | command | bar |
|---|---|---|
| unit suite | `dune runtest --force` | 467 ok, 0 FAIL |
| lattice equivalence | `dune exec zz_scratch_probe/clpequiv.exe` | 0 mismatches |
| corpus emission | `bash scripts/run_corpus.sh /tmp/corpus <out>` | 32/32 rc=0 |
| **IR byte-identity** | diff vs the pre-swap emission | **identical 32/32** |
| **coreutils IR byte-identity** | the 103-bin emission | **identical 103/103** |
| structural asserts | `bash scripts/check_allocas.sh <out>` | 160/0 |
| semantics (8-bin) | `run_semantic.sh` | 8/8 PASS |
| producer gauge | `census.exe` on ls | **improve** vs 771 tags/s |
| corpus wall | `clean_times.tsv` method, P-core pinned | **improve** vs 803 s |

## Method notes

- Emit the control (pre-swap) emission from the SAME tree before
  switching — do not reuse `/home/tovpr/backup/emissions/*` (stale).
- Pin every timing run: `taskset -c 0-11` (E-cores are 1.9× slower).
- The corpus wall gate is the whole point: **803 s → target < 600 s**
  (the "sub 10 minutes" goal), with A (lane scheduler) expected to carry
  most of it; B's contribution is measured here, honestly, whatever it is.

## If IR differs

Stop. A difference is a semantic change, and the domain is the product's
soundness carrier. Bisect with `clpequiv`'s op sweep first (per-op), then
per-module (fin_set → clp → composite). Do not re-baseline to make the
gate pass without identifying the divergence.
