# Spec: the word substrate — an int63 fast path behind the domain's existing seam

Branch: `word-substrate` (from main @ 753601b)
Grilling-settled 2026-09-05 (3 rounds, 7 questions).

## The problem

The abstract-domain arithmetic is **31.6% of every coreutils lift** (perf,
103 binaries, 176,957 samples) — the single largest identified bucket. Its
root cause is upstream of hike: BAP's `Word.t = {packed : Z.t}`
(`lib/bap-std/types/bap_bitvector.ml:56`) — **every word op is
arbitrary-precision, and values above 62 bits are always boxed**. This
domain's words are 64/65/129-bit, so *every* operation allocates.

## The measurement that settles the premise (op-COST, not op-COUNT)

`zz_scratch_probe/census.ml` (added by this lane) plus a standalone
microbenchmark:

| op | ns/op | minor words/op |
|---|---|---|
| `Word.add` (64-bit) | **110 ns** | **41.4** |
| `Word.mul` (64-bit) | 122 ns | 46.0 |
| `Word.compare` | 60 ns | 19.9 |
| `Word.lshift` (65-bit) | 40 ns | 11.0 |
| `Int64.add` | **0.3 ns** | **0.00** |
| `Int64.mul` | 0.8 ns | 0 |

~350× per-op. And the domain does **~16M ops per heavy sub**
(653M minor words ÷ ~41 words/op) = 5.7M ops/s against a core capable of
~1000M/s. The cost is *per operation*, not the number of operations.

**Fast-path hit rate, measured on real fixpoints** (census over all subs;
the bar set in grilling was ≥80%):

| binary | operands | small (fits int63) | wide |
|---|---|---|---|
| ls | 24,362 | **92.9%** | 7.1% |
| du | 38,320 | **94.0%** | 6.0% |
| cksum | 26,174 | **98.3%** | 1.7% |

Baseline gauge (`ls`, all subs): **771 tags/s, 1527 operands/s, 15.95 s
producer**.

## Decisions (grilling-settled)

1. **Representation: int63 immediate for small magnitudes + `Z.t` fallback.**
   Discrimination is by **value magnitude** (|v| ≤ 2⁶² − 1), *not* by
   declared width. This is the only framing that works: the domain
   genuinely constructs 129-bit words (`dom_size ~width:(2*width + 1)`
   at `cbat_clp.ml:65`; `mul_exact` sums widths to 129), so a
   width-based rule would exclude the very intermediates that exist. A
   64-bit word holding `-1120` is small; the fast path is chosen on
   value, never on type.
2. **Own the whole word layer.** `cbat_clp.ml:18` (`module W = Word`) is
   the chokepoint, but `cbat_word_ops`/`cbat_fin_set` also use `Word.t`
   directly and `WordSet.S` exposes `word` in its interface. The seam is
   `WordSet.S` + `Cbat_word_ops`: one hike-owned module satisfies it;
   `Cbat_clp`, `Cbat_fin_set`, `Cbat_clp_set_composite` and
   `Cbat_interval_tree` keep their own interfaces untouched.
   (A narrower "cache the hot constants" option was rejected: it leaves
   31.6% on the table.)
3. **Replace in `src/`, keep the referee in `clpequiv`.** No dual-track
   production code. `clpequiv.ml` **already inlines old (reference)
   implementations by design** — the Z-based reference moves there before
   the swap, so the differential lives in the test, not in production.
4. **Correctness bar:** `clpequiv` (extended: reference-vs-new across the
   dense `(width, base, step, cardn)` sweep) **plus** IR byte-identity on
   the 103-binary corpus **plus** the 467-check suite. IR byte-identity is
   non-negotiable: a silent divergence here is an unsound narrowing
   (the array_local class), not a crash.
5. **Census mechanism: extend `clpequiv`/`census`, do not touch the
   domain's dune stanza.** `cbat_vsa_domain` uses `pps ppx_bap` with **no
   cppo step**; adding `#ifdef VSA_DEBUG` there reproduces the documented
   "not an object" build breakage (`src/cbat_vsa/dune:60-69`). The
   sanctioned alternative (mirroring the cppo stanza) was considered and
   rejected as build-plumbing risk in a lane whose payoff is measured
   elsewhere.

## Work plan

- **T1 — Reference capture.** Move the current Z-based `Cbat_word_ops`
  implementations into `clpequiv.ml` as the reference, and extend
  `clpequiv`'s sweep to cross-check them. Gate: suite green, sweep reports
  0 mismatches against the *unmodified* production ops (the harness is
  validated before anything changes).
- **T2 — The module.** New `Cbat_word`: `Small of int` (unboxed int63) |
  `Big of Z.t`, with the `Word.t`-compatible operation set. Width is
  carried per value; the constructor enforces the magnitude split.
- **T3 — The swap.** `cbat_clp.ml` (`module W = Word` → the new module),
  then `cbat_word_ops`, `cbat_fin_set`, `cbat_clp_set_composite`. Keep
  `Word.t` only at BAP-facing edges (`Word` in signatures that BAP fills).
- **T4 — Verification.** `clpequiv` 0 mismatches; `dune runtest`
  467 ok; corpus 103/103 rc=0; **IR byte-identical 103/103** to the
  pre-swap emission; re-run the census gauge (expect a large tags/s
  improvement); re-measure corpus wall with `clean_times.tsv`'s method.
- **T5 — Record + re-baseline.** Update `AGENTS.md`'s validation state
  with fresh numbers; land the perf report's B entry as measured.

## Non-goals

- No change to the lattice's semantics, interfaces, or the `WordSet.S`
  signature's shape (only its `word` type's representation).
- No change to `cbat_vsa_domain`'s dune stanza.
- No width-based fast path (see decision 1).

## Risks

- **Unsound narrowing.** Mitigated by decision 4 (IR byte-identity is the
  oracle; the failure mode is silent, so identity is the gate).
- **The 7% wide path.** `dom_size`/`mul_exact`'s 129-bit intermediates
  stay on `Z.t`; if the census's 7% turns out to sit on the hottest path,
  the win shrinks proportionally. Re-census after T3.
- **Throughput gauge noise.** The census reports producer time for the
  whole binary; pin to P-cores (`taskset -c 0-11`) when comparing.
