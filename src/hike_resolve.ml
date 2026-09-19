(* The indirect-target resolution story: the class of every indirect
   call site, read from the TARGET's denotation — never a shape or a
   name.  [resolve_target] is the site predicate over the target's
   word set; [symtab_lookup] builds the lifted world's lookup (the
   symtab + the program's name map).  The CFG completion's dispatch
   rewrite reads its case pairs off the same denotation vocabulary. *)

open Bap.Std
module Vsa = Cbat_vsa
module Model = Hike_stack_model

(* The target-resolution predicate: the site's class over the
   target's denotation.  A singleton whose word names a lifted sub
   resolves ([Some tid] — the Resolved Call Site); a bounded
   multi-target set, a foreign singleton, and an unresolvable set all
   take the pointer call ([None]).  [lookup] answers "is this address
   a lifted sub?" (the symtab + the program's name map in
   production). *)
let resolve_target ~(lookup : int64 -> Tid.t option) (ws : Vsa.WordSet.t) :
    Tid.t option = match Model.singleton_i64 ws with
  | None -> None
  | Some v -> lookup v

(* The lifted world's lookup: a singleton address names a sub of this
   program through the symtab and the name map (a singleton FOREIGN
   address resolves to no sub). *)
let symtab_lookup ~(symtab : Symtab.t option)
    ~(name_tid : (string * Tid.t) list) (v : int64) : Tid.t option =
  match symtab with
  | Some symtab -> (
      match Symtab.find_by_start symtab (Word.of_int64 ~width:64 v) with
      | Some (name, _, _) ->
        Base.List.Assoc.find ~equal:String.equal name_tid name
      | None -> None)
  | None -> None
