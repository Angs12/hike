# T2 — The Cbat_word module: int63 immediate + Z fallback

Blocked by: T1
Blocks: T3

## Goal

One hike-owned word module implementing the operation set the domain uses,
with a value-magnitude fast path.

## Representation

```ocaml
type t = Small of int     (* |v| <= 2^62 - 1, unboxed immediate *)
       | Big   of Z.t     (* everything else *)
```

Discrimination is by **value magnitude, never by declared width** (spec
decision 1). Width is carried alongside where the domain needs it
(`Cbat_clp.t` keeps its own width discipline; the word module is the
numeric substrate, not the width authority).

## Operation set (from the domain's actual usage)

`cbat_clp.ml` uses: add sub mul div modulo smodulo neg lnot logand logor
logxor lshift rshift arshift compare extract is_zero is_one pred succ
of_int zero one ones bitwidth min max signed.
`cbat_word_ops.ml` uses the same plus `gcd_exn`, `lcm_exn`, `to_int_exn`.

## Rules

- Every op: if both operands are `Small` and the result's magnitude fits,
  compute in machine ints and return `Small` — **zero allocation**.
- Otherwise compute via `Z.t` and return `Big` (or `Small` if the result
  narrowed back into range — normalization is permitted, never required).
- Signedness: the domain norms to non-negative (BAP invariant,
  `bitvec.ml:5`); the fast path assumes the non-negative representation
  and falls back to `Z` for anything it cannot prove.
- **Never** silently drop width: `extract`/`concat` keep the current
  semantics exactly — this is what `clpequiv` pins.

## Gate

- Builds under both profiles (`dune build` and `--profile vsa-debug`).
- `clpequiv` (T1's harness) green against the reference for the module's
  own op sweep.
- Still **unused by the domain** in this ticket — T3 wires it in.
