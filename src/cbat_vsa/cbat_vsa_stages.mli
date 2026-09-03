(* Per-stage profiling; [time] never changes the wrapped result. *)

(* True in the timing build. *)
val enabled : bool

val denote_calls : int ref
val join_calls : int ref
val equal_calls : int ref
val widen_calls : int ref
val walk_calls : int ref

(* Walk-schedule metrics: pops, blocks, truncs, max_pops. *)
val walk_pops : int ref
val walk_blocks : int ref
val walk_truncs : int ref
val walk_max_pops : int ref

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

(* Commit one walk's schedule metrics. *)
val bump_walk_pops :
  pops:int -> blocks:int -> truncated:bool -> unit -> unit

(* Print totals and call counts. *)
val report : string -> unit
