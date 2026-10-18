open Bap.Std

type 'a solution = {
  before : 'a Tid.Map.t;
  after : 'a Tid.Map.t;
}

val run :
  graph:Graphs.Tid.t ->
  sub:sub term ->
  rev:bool ->
  initial:'a Tid.Map.t ->
  default:'a ->
  equal:('a -> 'a -> bool) ->
  merge:('a -> 'a -> 'a) ->
  def:('a -> def term -> 'a) ->
  phi:('a -> phi term -> 'a) ->
  jmp:('a -> jmp term -> 'a) ->
  'a solution

(* Backward may-liveness over [Var.Set.t], with each block's transfer
   compiled once to a gen/kill pair.  [def] and [phi] give an element's
   (writes, reads), as does [jmp]; a write kills the live set, so a
   memory def's writes are the caller's to leave empty.  The result is
   what [run ~rev:true] gives with the equivalent set-transfer closures
   (a block's transfer is idempotent, so no local closure is needed). *)
val liveness :
  graph:Graphs.Tid.t ->
  sub:sub term ->
  initial:Var.Set.t Tid.Map.t ->
  def:(def term -> Var.Set.t * Var.Set.t) ->
  phi:(phi term -> Var.Set.t * Var.Set.t) ->
  jmp:(jmp term -> Var.Set.t * Var.Set.t) ->
  Var.Set.t solution

(* A monotone rule over SSA versions: [fire] adds versions to the
   solution given what it holds, and re-runs whenever a version in
   [reads] joins.  Facts of a version, not of a program point, so the
   solution is one set with no per-block state. *)
type rule = {
  reads : var list;
  fire : holds:(var -> bool) -> add:(var -> unit) -> unit;
}

(* The least set containing the seeds and closed under the rules, each
   rule fired once up front and again per joining read.  Compile the
   rules once, then solve per seed list. *)
val closure : rule list -> var list -> var list
