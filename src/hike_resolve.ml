(* Indirect-target resolution: the class of every indirect call site,
   read from the target's denotation — never a shape or a name. *)

open Bap.Std
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

(* A singleton address names a sub of this program through the symtab
   and the name map; a foreign address resolves to no sub. *)
let symtab_lookup ~(symtab : Symtab.t option)
    ~(name_tid : (string * Tid.t) list) (v : int64) : Tid.t option =
  match symtab with
  | Some symtab -> (
      match Symtab.find_by_start symtab (Word.of_int64 ~width:64 v) with
      | Some (name, _, _) ->
        Base.List.Assoc.find ~equal:String.equal name_tid name
      | None -> None)
  | None -> None
