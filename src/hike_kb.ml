(* Per-sub VSA results in the KB. Order is map extension, join is map union. *)

open Bap.Std

module KB = Bap_knowledge.Knowledge
(* The record home (S10b). *)
module Model = Hike_stack_model

let run_cls = KB.Class.declare ~package:"hike" "run" ()

(* Conflicting infos for one sub. *)
type KB.conflict += Vsa_info_conflict of Tid.t * Model.vsa_info * Model.vsa_info

let () =
  KB.Conflict.register_printer (function
    | Vsa_info_conflict (tid, i1, i2) ->
        Some
          (Printf.sprintf
             "hike: vsa-info conflict on sub %s: two different VSA results were provided for the same sub (offsets %d vs %d) — the analyses disagree, refusing to drop either"
             (Tid.name tid)
             (Core.Map.length i1.Model.offsets)
             (Core.Map.length i2.Model.offsets))
    | _ -> None)

(* Joins two infos; differing infos conflict. *)
let info_join (tid : Tid.t) (i1 : Model.vsa_info) (i2 : Model.vsa_info) :
    (Model.vsa_info, KB.conflict) result =
  (* Equality is the only order infos have; anything else conflicts. *)
  if Model.equal_vsa_info i1 i2 then Ok i1
  else Error (Vsa_info_conflict (tid, i1, i2))

(* Orders maps by extension. *)
let map_order (m1 : Model.vsa_info Tid.Map.t)
    (m2 : Model.vsa_info Tid.Map.t) : KB.Order.partial =
  if Base.phys_equal m1 m2 || Core.Map.equal Model.equal_vsa_info m1 m2
  then KB.Order.EQ
  else
    let included_in a b =
      Core.Map.fold a ~init:true ~f:(fun ~key:tid ~data:i1 acc ->
          acc
          &&
          match Core.Map.find b tid with
          | Some i2 -> Model.equal_vsa_info i1 i2
          | None -> false)
    in
    if included_in m1 m2 then KB.Order.LT
    else if included_in m2 m1 then KB.Order.GT
    else KB.Order.NC

(* Unions maps; shared subs join per [info_join]. *)
let map_join (m1 : Model.vsa_info Tid.Map.t)
    (m2 : Model.vsa_info Tid.Map.t) :
    (Model.vsa_info Tid.Map.t, KB.conflict) result =
  match map_order m1 m2 with
  | EQ -> Ok m1
  | LT -> Ok m2
  | GT -> Ok m1
  | NC -> (
      (* First conflict wins; the base extends. *)
      let base, conflict =
        Core.Map.fold m2 ~init:(m1, None)
          ~f:(fun ~key:tid ~data:i2 (base, conflict) ->
            match Core.Map.find base tid with
            | None -> (Core.Map.set base ~key:tid ~data:i2, conflict)
            | Some i1 -> (
                match info_join tid i1 i2 with
                | Ok _ -> (base, conflict) (* Keeps [m1]'s entry. *)
                | Error c -> (
                  match conflict with
                  | None -> (base, Some c)
                  | Some _ -> (base, conflict)))) in
      match conflict with
      | Some c -> Error c
      | None -> Ok base)

let vsa_info_slot =
  KB.Class.property ~package:"hike" run_cls "vsa-info"
    (KB.Domain.define
       ~inspect:(fun _ -> Base.Sexp.Atom "hike:vsa-info")
       ~join:map_join
       ~empty:Tid.Map.empty
       ~order:map_order
       "hike:vsa-info")

(* Reads the current VSA map. The cell is the monad-escape idiom: the KB
   callback cannot return a value, so it parks the map in a local ref. *)
let vsa_info () : Model.vsa_info Tid.Map.t =
  let r = ref Tid.Map.empty in
  Toplevel.exec
    (KB.bind (KB.Object.read run_cls "hike-run") ~f:(fun obj ->
         KB.bind (KB.collect vsa_info_slot obj) ~f:(fun m ->
             r := m;
             KB.return ())));
  !r

(* The ONE vsa_info lookup. Absence means "no tags" (the empty info): the
   identity rule every consumer used to restate with its own default. The
   pipeline's vsa pass provides every sub; fixtures state untagged subs
   simply by not providing. *)
let info_of_sub (tid : Tid.t) : Model.vsa_info =
  match Core.Map.find (vsa_info ()) tid with
  | Some info -> info
  | None -> Model.empty_vsa_info

(* Stores [vmap] in the slot. *)
let provide (vmap : Model.vsa_info Tid.Map.t) : unit =
  Toplevel.exec
    (KB.bind (KB.Object.read run_cls "hike-run") ~f:(fun obj ->
         KB.provide vsa_info_slot obj vmap))
