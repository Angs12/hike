(* The per-stage profiling counters — DEBUG adapter (the vsa-debug profile).

   The Q6 harness: the fixpoint's per-visit cost is exactly
   (denotation + join + equal + widen) plus the deep walk, and nothing in
   the tree could previously attribute time between them. That gap is how
   three separate changes this session got reported as "wins" while
   sitting inside measurement noise.

   Selected ONLY under --profile vsa-debug (src/cbat_vsa/dune); every
   other profile links [cbat_vsa_stages_prod.ml], the no-op twin with the
   same interface. AGENTS.md §6. *)

let enabled = true

let denote_calls = ref 0
let join_calls = ref 0
let equal_calls = ref 0
let widen_calls = ref 0
let walk_calls = ref 0

let t_denote = ref 0.
let t_join = ref 0.
let t_equal = ref 0.
let t_widen = ref 0.
let t_walk = ref 0.

let reset () =
  denote_calls := 0; join_calls := 0; equal_calls := 0; widen_calls := 0;
  walk_calls := 0;
  t_denote := 0.; t_join := 0.; t_equal := 0.; t_widen := 0.;
  t_walk := 0.

(* [time which f]: run [f], accumulating its wall time into [which]. The
   clock read is [Unix.gettimeofday] (~50ns) — negligible against the
   operations being timed (a block denotation, an AI.join, a widening). *)
let time (which : [ `Denote | `Equal | `Join | `Walk | `Widen ]) (f : unit -> 'a)
  : 'a =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let dt = Unix.gettimeofday () -. t0 in
  (match which with
   | `Denote -> incr denote_calls; t_denote := !t_denote +. dt
   | `Join -> incr join_calls; t_join := !t_join +. dt
   | `Equal -> incr equal_calls; t_equal := !t_equal +. dt
   | `Widen -> incr widen_calls; t_widen := !t_widen +. dt
   | `Walk -> incr walk_calls; t_walk := !t_walk +. dt);
  r

let report (label : string) : unit =
  Printf.printf
    "STAGES %s: denote %7.3fs/%d  join %7.3fs/%d  equal %7.3fs/%d  \
     widen %7.3fs/%d  walk %7.3fs/%d\n%!"
    label !t_denote !denote_calls !t_join !join_calls !t_equal !equal_calls
    !t_widen !widen_calls !t_walk !walk_calls
