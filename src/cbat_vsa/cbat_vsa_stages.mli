(* Per-stage profiling; [time] never changes the wrapped result. *)

val denote_calls : int ref
val join_calls : int ref
val equal_calls : int ref
val widen_calls : int ref
val walk_calls : int ref

(* Count one walk. *)
val incr_walk : unit -> unit

(* Accumulated per-stage seconds. *)
val t_denote : float ref
val t_walk : float ref
val t_join : float ref
val t_widen : float ref
val t_equal : float ref

val t_scaffold : float ref
val scaffold_calls : int ref

(* Glue metrics. *)
val t_glue : float ref
val glue_calls : int ref

(* Zero every counter. *)
val reset : unit -> unit

(* Run [f]; accumulate wall time. *)
val time :
  [ `Denote | `Equal | `Glue | `Join | `Scaffold | `Walk | `Widen ] ->
  (unit -> 'a) -> 'a

(* Cell-landmark census: acquisitions at cell meets and Finite-arm
   consumptions at widening heads. The debug adapter accumulates for the
   whole process (reset leaves them); the prod adapter stays 0. *)

(* Print totals and call counts. *)
val report : string -> unit

