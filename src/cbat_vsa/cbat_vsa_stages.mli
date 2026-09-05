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

(* Budget metrics: walks launched under the 256 cap and the pop delta
   vs that cap for those walks. *)
val budget_hits : int ref
val pops_saved : int ref

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

(* Commit one walk's schedule metrics; [budget_cap] is the steps cap the
   walk ran under (the per-SCC budget may have lowered it below 256). *)
val bump_walk_pops :
  pops:int -> blocks:int -> truncated:bool -> budget_cap:int -> unit -> unit

(* Print totals and call counts. *)
val report : string -> unit

(* Snapshot: denote_t, denote_n, walk_t, walk_n, join_t, join_n, pops,
   blocks, truncs, max_pops, minor_words. No-ops return zeros. *)
val stats :
  unit ->
  float * int * float * int * float * int * int * int * int * int * float

(* Memo accounting: lookups, hits, stale, stores, empty-map lookups. *)
val memo_stats : unit -> int * int * int * int * int

