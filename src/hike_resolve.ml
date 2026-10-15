(* Indirect-target resolution: the class of every indirect call site,
   read from the target's denotation — never a shape or a name. *)

open Bap.Std
open Core
module Vsa = Cbat_vsa
module Model = Hike_stack_model

(* A singleton whose word names a lifted sub resolves ([Some tid]); a
   bounded multi-target set, a foreign singleton, and an unresolvable
   set all take the pointer call ([None]).  [lookup] answers "is this
   address a lifted sub?". *)
let resolve_target ~(lookup : int64 -> Tid.t option) (ws : Vsa.WordSet.t) :
    Tid.t option = match Model.singleton_i64 ws with
  | None -> None
  | Some v -> lookup v
