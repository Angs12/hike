(* Debug timing adapter; linked only under --profile vsa-debug. *)

let denote_calls = ref 0
let join_calls = ref 0
let equal_calls = ref 0
let widen_calls = ref 0
let walk_calls = ref 0

let incr_walk () = incr walk_calls

let t_denote = ref 0.
let t_join = ref 0.
let t_equal = ref 0.
let t_widen = ref 0.
let t_walk = ref 0.


let t_scaffold = ref 0.
let scaffold_calls = ref 0

(* Cell-landmark census, accumulated for the whole process; [reset]
   (per-solve) leaves them so every STAGES line carries the total. *)

let t_glue = ref 0.
let glue_calls = ref 0

(* Allocation baseline for [report]. *)
let gc0 = ref (Gc.quick_stat ())

let reset () =
  denote_calls := 0; join_calls := 0; equal_calls := 0; widen_calls := 0;
  walk_calls := 0;
  t_denote := 0.; t_join := 0.; t_equal := 0.; t_widen := 0.;
  t_walk := 0.;
  t_scaffold := 0.; scaffold_calls := 0;
  t_glue := 0.; glue_calls := 0;
  gc0 := Gc.quick_stat ()

(* Run [f]; accumulate wall time. *)
let time (which : [ `Denote | `Equal | `Glue | `Join | `Scaffold | `Walk | `Widen ])
    (f : unit -> 'a) : 'a =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let dt = Unix.gettimeofday () -. t0 in
  (match which with
   | `Denote -> incr denote_calls; t_denote := !t_denote +. dt
   | `Join -> incr join_calls; t_join := !t_join +. dt
   | `Equal -> incr equal_calls; t_equal := !t_equal +. dt
   | `Widen -> incr widen_calls; t_widen := !t_widen +. dt
   | `Walk -> incr walk_calls; t_walk := !t_walk +. dt
   | `Scaffold -> incr scaffold_calls; t_scaffold := !t_scaffold +. dt
   | `Glue -> incr glue_calls; t_glue := !t_glue +. dt);
  r

(* Print totals, call counts, and GC deltas. *)
let gc_minor_words () =
  (Gc.quick_stat ()).Gc.minor_words -. (!gc0).Gc.minor_words
let gc_major_words () =
  (Gc.quick_stat ()).Gc.major_words -. (!gc0).Gc.major_words
let gc_promoted_words () =
  (Gc.quick_stat ()).Gc.promoted_words -. (!gc0).Gc.promoted_words

(* Linked only in the vsa-debug profile. *)
#ifdef VSA_DEBUG
let report (label : string) : unit =
  Printf.printf
    "STAGES %s: denote %7.3fs/%d  join %7.3fs/%d  equal %7.3fs/%d  \
     widen %7.3fs/%d  walk %7.3fs/%d  scaffold %7.3fs/%d  glue %7.3fs/%d  \
     GC %s: minor %.0f  major %.0f  promoted %.0f\n%!"
    label !t_denote !denote_calls !t_join !join_calls !t_equal !equal_calls
    !t_widen !widen_calls !t_walk !walk_calls !t_scaffold !scaffold_calls
    !t_glue !glue_calls
    label (gc_minor_words ()) (gc_major_words ()) (gc_promoted_words ())
#endif
