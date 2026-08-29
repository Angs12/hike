# 01 — .mli + rename + helpers split

**Depends on:** none
**Blocks:** 02, 03, 04

Split `src/hike_vsa_relevance.ml:20-203` into four pure helpers inside one file plus `src/hike_vsa_relevance.mli` documenting the two-tag contract (`stack_access` seed, `relevant` closure over defs+phis).

Tasks:
- Create `hike_vsa_relevance.mli` exposing `stack_access`, `relevant` (re-export), `dynamic_alloc`, `has_stack_access : def term -> bool`, `is_sp : Theory.Target.t -> var -> bool`, `analyze : var -> sub term -> sub term`.
- Rename `direct_sp` -> `stack_access` with new uuid (clean break), drop alias, update header comment.
- Extract helpers: `collect_def_maps` (one `Term.visitor` pass), `forward_vars` (SP-only fixpoint, `Var.base` helper, assert `sp != fp`), `backward_slice` (phis included), `detect_dynamic_alloc` (Exp.mapper).
- Keep `Exp.free_vars` for sets, add invariant comments on `Graphlib.fixpoint` params.

Gate: `dune build` green, `dump_tags.exe` tag diff script ready for 02.
