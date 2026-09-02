(* The per-stage profiling counters — PRODUCTION (no-op) adapter.

   Selected by dune in every profile EXCEPT vsa-debug (see
   src/cbat_vsa/dune). Every function here is a no-op the compiler erases,
   so the production fixpoint pays nothing: no refs, no clock reads, no
   env lookups.

   The debug twin [cbat_vsa_stages_debug_src.ml] has the SAME interface,
   which is what lets [cbat_vsa.ml] call these unconditionally.
   AGENTS.md §6: no debug instrumentation in production. *)

let enabled = false

let denote_calls = ref 0
let join_calls = ref 0
let equal_calls = ref 0
let widen_calls = ref 0
let walk_calls = ref 0

(* L2 — the walk-schedule metric refs (interface parity with the debug
   twin; production never reads them). *)
let walk_pops = ref 0
let walk_blocks = ref 0
let walk_truncs = ref 0
let walk_max_pops = ref 0

let t_scaffold = ref 0.
let scaffold_calls = ref 0

let t_glue = ref 0.
let glue_calls = ref 0

let reset () = ()

let time (_which : [ `Denote | `Equal | `Glue | `Join | `Scaffold | `Walk | `Widen ])
    (f : unit -> 'a) : 'a = f ()

let bump_walk_pops ~pops:_ ~blocks:_ ~truncated:_ () = ()

let report (_label : string) : unit = ()
