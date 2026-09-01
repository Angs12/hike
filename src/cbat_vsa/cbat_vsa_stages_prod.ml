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

let reset () = ()

let time (_which : [ `Denote | `Equal | `Join | `Walk | `Widen ])
    (f : unit -> 'a) : 'a = f ()

let report (_label : string) : unit = ()
