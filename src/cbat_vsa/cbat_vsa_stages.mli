(* The per-stage profiling interface — ONE contract, two adapters.

   The debug adapter ([cbat_vsa_stages_debug_src.ml]) times and
   accumulates; the production adapter ([cbat_vsa_stages_prod.ml]) is a
   no-op the compiler erases. [src/cbat_vsa/dune] selects between them by
   profile and copies the chosen one to the generated
   [cbat_vsa_stages.ml], so [cbat_vsa.ml] calls these unconditionally and
   production carries no instrumentation (AGENTS.md §6).

   INVARIANT the callers rely on: [time] never changes the RESULT of the
   computation it wraps — it only accumulates a duration. Both adapters
   must preserve that, so the two profiles emit byte-identical IR. *)

(* [enabled]: is this the timing build? *)
val enabled : bool

val denote_calls : int ref
val join_calls : int ref
val equal_calls : int ref
val widen_calls : int ref
val walk_calls : int ref

(* [reset ()]: zero every counter (once per sub, at fixpoint entry). *)
val reset : unit -> unit

(* [time which f]: run [f], accumulating its wall time into [which]'s
   total. In the no-op adapter this is exactly [f ()]. *)
val time :
  [ `Denote | `Equal | `Join | `Walk | `Widen ] -> (unit -> 'a) -> 'a

(* [report label]: print the per-stage totals and call counts. *)
val report : string -> unit
