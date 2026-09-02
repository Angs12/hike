(* Knowledge-base transfer for per-sub VSA results.

   THE SLOT: one KB property ([vsa_info_slot]) on the hike run class,
   holding the whole per-sub map. Its DOMAIN is the whole point of this
   module (the KB store fix):

   - [order] is MAP EXTENSION — [m1 <:= m2] iff every sub in [m1] is in
     [m2] with the SAME [vsa_info]. So a second provide that adds subs
     the first did not have is a MONOTONE update (the KB keeps both).
   - [join] is MAP UNION with the SAME rule per collided sub: equal
     infos take either; DIFFERING non-empty infos for the same sub are a
     REAL knowledge conflict, surfaced by the KB as [Toplevel.Conflict]
     (the [Join] conflict carries both values in its printer) — never
     silently dropped.

   The old design hand-wrote a silent drop around a flat domain
   ([else if ... then () else ()] — a second, different map was discarded
   without a sound), which spawned two workarounds elsewhere: the vsa
   pass's re-entrancy guard and the A4 test's tid-borrowing. With the
   join domain, providing again is either a no-op (empty map), an
   extension (new subs), an idempotent re-write (the same map), or a
   LOUD conflict (two different analyses of the same sub) — the KB's
   own [Non_monotonic_update] machinery, not a hand-rolled guard. *)

open Bap.Std

module KB = Bap_knowledge.Knowledge

let run_cls = KB.Class.declare ~package:"hike" "run" ()

(* [info_order i1 i2]: EQ when equal, LT/GT never (a [vsa_info] is a
   complete analysis result — one is never a strict subset of another),
   NC when they differ. *)
let info_order (i1 : Convutils.vsa_info) (i2 : Convutils.vsa_info) :
    KB.Order.partial =
  if Convutils.equal_vsa_info i1 i2 then KB.Order.EQ else KB.Order.NC

(* The conflict two vsa analyses produce different [vsa_info] for the
   SAME sub — surfaced by the KB's join machinery as
   [Toplevel.Conflict], never silently dropped. *)
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

(* [info_join i1 i2]: equal infos join to either; differing infos are a
   conflict (two producers disagree about one sub's VSA result — that
   is a bug to surface, not data to drop). *)
let info_join (tid : Tid.t) (i1 : Convutils.vsa_info) (i2 : Convutils.vsa_info) :
    (Convutils.vsa_info, KB.conflict) result =
  match info_order i1 i2 with
  | EQ -> Ok i1
  | NC -> Error (Vsa_info_conflict (tid, i1, i2))
  | LT -> Ok i2
  | GT -> Ok i1

(* [map_order m1 m2]: MAP EXTENSION — [m1] is below [m2] iff [m2]
   carries every sub [m1] has, with the same info. The empty map is the
   bottom. *)
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

(* [map_join m1 m2]: MAP UNION — subs only one side has survive as-is;
   a sub both sides have joins per [info_join] (equal: either;
   differing: a real conflict). *)
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
              | Ok _ -> () (* equal — keep m1's *)
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

(* Read the current VSA map (empty if none provided). *)
let vsa_info () : Convutils.vsa_info Tid.Map.t =
  let r = ref Tid.Map.empty in
  Toplevel.exec
    (KB.bind (KB.Object.read run_cls "hike-run") ~f:(fun obj ->
         KB.bind (KB.collect vsa_info_slot obj) ~f:(fun m ->
             r := m;
             KB.return ())));
  !r

(* [provide vmap]: store [vmap] into the KB slot. The DOMAIN decides the
   outcome — an empty map is a KB no-op, an extension/new map is a
   monotone update, a re-write of the same map is idempotent, and two
   DIFFERENT infos for the same sub raise [Toplevel.Conflict] (loud —
   the silent drop is gone). *)
let provide (vmap : Convutils.vsa_info Tid.Map.t) : unit =
  Toplevel.exec
    (KB.bind (KB.Object.read run_cls "hike-run") ~f:(fun obj ->
         KB.provide vsa_info_slot obj vmap))
