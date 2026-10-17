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
