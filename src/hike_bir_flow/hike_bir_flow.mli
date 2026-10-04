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
