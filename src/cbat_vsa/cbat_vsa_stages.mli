(* The per-stage profiling interface — ONE contract, two adapters.

   The debug adapter ([cbat_vsa_stages_debug_src.ml]) times and
   accumulates; the production adapter ([cbat_vsa_stages_prod.ml]) is a
   no-op the compiler erases. [src/cbat_vsa/dune] selects between them by
   profile and copies the chosen one to the generated
   [cbat_vsa_stages.ml], so [cbat_vsa.ml] calls these unconditionally and
   production carries no instrumentation (AGENTS.md §6).

   INVARIANT the callers rely on: [time] never changes the RESULT of the
   computation it wraps — it only accumulates a duration. Both adapters
   must preserve that, so the two profiles emit byte-identical IR.

   The same invariant covers the L2 walk-schedule hooks: [bump_walk_
   pops] is a pure accumulator in the debug adapter and the identity in
   production — a walk's RESULT never depends on it. *)

(* [enabled]: is this the timing build? *)
val enabled : bool

val denote_calls : int ref
val join_calls : int ref
val equal_calls : int ref
val widen_calls : int ref
val walk_calls : int ref

(* L2 — the walk-schedule metrics (debug adapter accumulates; prod is 0):
   pops (Kildall pop counter), blocks (distinct visited), truncs (walks
   stopped at the 256 cap), max_pops (the largest single walk). *)
val walk_pops : int ref
val walk_blocks : int ref
val walk_truncs : int ref
val walk_max_pops : int ref

val t_scaffold : float ref
val scaffold_calls : int ref

(* L2 sub-attribution — the GLUE sub-bucket (the scaffold's remainder
   after every named stage): the visit prologue (the [get], the Graphlib
   pred listing, the sol snapshot), the per-pred landmark bindings, and
   the [set] path (the version bump + the sol_map write + the context
   rebind).  In production this is the identity. *)
val t_glue : float ref
val glue_calls : int ref

(* [reset ()]: zero every counter (once per sub, at fixpoint entry). *)
val reset : unit -> unit

(* [time which f]: run [f], accumulating its wall time into [which]'s
   total. In the no-op adapter this is exactly [f ()]. *)
val time :
  [ `Denote | `Equal | `Glue | `Join | `Scaffold | `Walk | `Widen ] ->
  (unit -> 'a) -> 'a

(* [bump_walk_pops ~pops ~blocks ~truncated ()]: commit ONE walk's
   schedule metrics (the debug adapter counts pops in the transfer
   closure and commits once per walk; the prod adapter is the identity). *)
val bump_walk_pops :
  pops:int -> blocks:int -> truncated:bool -> unit -> unit

(* [report label]: print the per-stage totals and call counts. *)
val report : string -> unit
