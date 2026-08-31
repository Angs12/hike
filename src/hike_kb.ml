(* Knowledge-base transfer for per-sub VSA results. Stores the whole VSA map in a single KB slot; consumers read it as a plain map via [vsa_info ()]. *)

open Bap.Std
module Vsa = Cbat_vsa

module KB = Bap_knowledge.Knowledge

let run_cls = KB.Class.declare ~package:"hike" "run" ()

(* Flat domain: equality join makes a second identical provide a no-op. *)
let vsa_info_slot =
  KB.Class.property ~package:"hike" run_cls "vsa-info"
    (KB.Domain.flat
       ~empty:Tid.Map.empty
       ~equal:(Core.Map.equal Convutils.equal_vsa_info)
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

(* Store the VSA map. Idempotent if the same map is provided twice. *)
let provide (vmap : Convutils.vsa_info Tid.Map.t) : unit =
  let cur = vsa_info () in
  if Core.Map.is_empty cur then
    Toplevel.exec
      (KB.bind (KB.Object.read run_cls "hike-run") ~f:(fun obj ->
           KB.provide vsa_info_slot obj vmap))
  else if Core.Map.equal Convutils.equal_vsa_info cur vmap then ()
  else ()

(* VSA solution map: per-sub fixpoint solution (for precise stack-arg Mem at call sites) *)
let vsa_sol_tbl : (Tid.t, Cbat_vsa.vsa_sol) Hashtbl.t = Hashtbl.create 16

let vsa_sol () : (Tid.t * Cbat_vsa.vsa_sol) list =
  Hashtbl.fold (fun k v acc -> (k,v)::acc) vsa_sol_tbl []

let provide_sol (sols : (Tid.t * Cbat_vsa.vsa_sol) list) : unit =
  List.iter (fun (tid, sol) -> Hashtbl.replace vsa_sol_tbl tid sol) sols

let add_sol (tid : Tid.t) (sol : Cbat_vsa.vsa_sol) : unit =
  Hashtbl.replace vsa_sol_tbl tid sol
