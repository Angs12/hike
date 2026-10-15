(* Per-stage profiling; [time] never changes the wrapped result. *)

(* Count one walk. *)
val incr_walk : unit -> unit

(* Zero every counter. *)
val reset : unit -> unit

(* Run [f]; accumulate wall time. *)
val time :
  [ `Denote | `Equal | `Glue | `Join | `Scaffold | `Walk | `Widen ] ->
  (unit -> 'a) -> 'a

(* Print totals and call counts. *)
val report : string -> unit
