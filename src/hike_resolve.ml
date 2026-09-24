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

(* The program's sub-name -> tid table, the lookup's name side; tid
   labels carry separators the symbol table spells without.  Built
   once per program, consulted per resolution. *)
let name_table_of (prog : program term) : Tid.t String.Map.t =
  Term.enum sub_t prog
  |> Seq.fold ~init:String.Map.empty ~f:(fun acc s ->
         Core.Map.set acc
           ~key:(Model.sanitize_tid_name (Tid.name (Term.tid s)))
           ~data:(Term.tid s))

(* The program-wide lookup: a singleton address names a sub of this
   program through the symtab and the name table; a foreign address
   resolves to no sub. *)
let symtab_lookup ~(symtab : Symtab.t option)
    ~(table : Tid.t String.Map.t) : int64 -> Tid.t option =
  match symtab with
  | Some symtab ->
    (fun v ->
       match Symtab.find_by_start symtab (Word.of_int64 ~width:64 v) with
       | Some (name, _, _) -> Core.Map.find table name
       | None -> None)
  | None -> fun _ -> None
