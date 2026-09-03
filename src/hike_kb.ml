(* Per-sub VSA results in the KB. Order is map extension, join is map union. *)

open Bap.Std

module KB = Bap_knowledge.Knowledge

let run_cls = KB.Class.declare ~package:"hike" "run" ()

(* Compares two infos: equal or incomparable. *)
let info_order (i1 : Convutils.vsa_info) (i2 : Convutils.vsa_info) :
    KB.Order.partial =
  if Convutils.equal_vsa_info i1 i2 then KB.Order.EQ else KB.Order.NC

(* Conflicting infos for one sub. *)
type KB.conflict += Vsa_info_conflict of Tid.t * Convutils.vsa_info * Convutils.vsa_info

let () =
  KB.Conflict.register_printer (function
    | Vsa_info_conflict (tid, i1, i2) ->
        Some
          (Printf.sprintf
             "hike: vsa-info conflict on sub %s: two different VSA results               were provided for the same sub (offsets %d vs %d) — the               analyses disagree, refusing to drop either"
             (Tid.name tid)
             (Core.Map.length i1.Convutils.offsets)
             (Core.Map.length i2.Convutils.offsets))
    | _ -> None)

(* Joins two infos; differing infos conflict. *)
let info_join (tid : Tid.t) (i1 : Convutils.vsa_info) (i2 : Convutils.vsa_info) :
    (Convutils.vsa_info, KB.conflict) result =
  match info_order i1 i2 with
  | EQ -> Ok i1
  | NC -> Error (Vsa_info_conflict (tid, i1, i2))
  | LT -> Ok i2
  | GT -> Ok i1

(* Orders maps by extension. *)
let map_order (m1 : Convutils.vsa_info Tid.Map.t)
    (m2 : Convutils.vsa_info Tid.Map.t) : KB.Order.partial =
  if Base.phys_equal m1 m2 || Core.Map.equal Convutils.equal_vsa_info m1 m2
  then KB.Order.EQ
  else
    let included_in a b =
      Core.Map.fold a ~init:true ~f:(fun ~key:tid ~data:i1 acc ->
          acc
          &&
          match Core.Map.find b tid with
          | Some i2 -> Convutils.equal_vsa_info i1 i2
          | None -> false)
    in
    if included_in m1 m2 then KB.Order.LT
    else if included_in m2 m1 then KB.Order.GT
    else KB.Order.NC

(* Unions maps; shared subs join per [info_join]. *)
let map_join (m1 : Convutils.vsa_info Tid.Map.t)
    (m2 : Convutils.vsa_info Tid.Map.t) :
    (Convutils.vsa_info Tid.Map.t, KB.conflict) result =
  match map_order m1 m2 with
  | EQ -> Ok m1
  | LT -> Ok m2
  | GT -> Ok m1
  | NC -> (
      let base = ref m1 in
      let conflict = ref None in
      Core.Map.iteri m2 ~f:(fun ~key:tid ~data:i2 ->
          match Core.Map.find !base tid with
          | None -> base := Core.Map.set !base ~key:tid ~data:i2
          | Some i1 -> (
              match info_join tid i1 i2 with
              | Ok _ -> () (* Keeps [m1]'s entry. *)
              | Error c -> if !conflict = None then conflict := Some c));
      match !conflict with
      | Some c -> Error c
      | None -> Ok !base)

let vsa_info_slot =
  KB.Class.property ~package:"hike" run_cls "vsa-info"
    (KB.Domain.define
       ~inspect:(fun _ -> Base.Sexp.Atom "hike:vsa-info")
       ~join:map_join
       ~empty:Tid.Map.empty
       ~order:map_order
       "hike:vsa-info")

(* Reads the current VSA map. *)
let vsa_info () : Convutils.vsa_info Tid.Map.t =
  let r = ref Tid.Map.empty in
  Toplevel.exec
    (KB.bind (KB.Object.read run_cls "hike-run") ~f:(fun obj ->
         KB.bind (KB.collect vsa_info_slot obj) ~f:(fun m ->
             r := m;
             KB.return ())));
  !r

(* Stores [vmap] in the slot. *)
let provide (vmap : Convutils.vsa_info Tid.Map.t) : unit =
  Toplevel.exec
    (KB.bind (KB.Object.read run_cls "hike-run") ~f:(fun obj ->
         KB.provide vsa_info_slot obj vmap))
