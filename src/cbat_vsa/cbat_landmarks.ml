(* Landmark-directed widening — Simon & King "Widening Polyhedra with Landmarks" (APLAS 2006)

   v1: dynamic rung extensions — landmarks are extra thresholds.
   Faithful port will later replace this with Listing 4 extrapolation, but v1
   already makes LM F1 exact (K+1) and keeps the threshold ladder for other widths.

   API matches the spec's issues 01-05 so later wiring can be swapped without churn.
*)

open Bap.Std
open Core_kernel

(* per-(var, bound, is_upper) entry; smaller distance wins (updateLandmark) *)
type lm_entry = { bound : Word.t; is_upper : bool; dist : int option }

let cap = 1 lsl 40
let cap_distance (d : int) : int = min d cap
let distance_words (a : Word.t) (b : Word.t) : int =
  let diff = Word.sub b a in
  try Word.to_int_exn diff with _ -> cap
  (* if word value > int range, cap *)

(* Global landmark environment — per Var.base -> sorted deduped Word.t list.
   Head attribution is skipped in v1 (single-loop tests don't need it); the
   table is global.  v2 will add per-head scoping.  Spec v2 keeps the global
   table as the sound fallback (per-var disabled boundaries) while also
   exposing the per-head API. *)
let table : (Var.t, lm_entry list) Hashtbl.t = Hashtbl.create (module Var)

let current_head : Tid.t option ref = ref None

(* spec v2 aliases *)
let current_lm_head : Tid.t option ref = current_head
let landmark_env : (Tid.t, (Var.t * Word.t * int * int option) list) Hashtbl.t ref =
  ref (Hashtbl.create (module Tid))

let is_lm_sub : bool ref = ref false
let head_table : (Tid.t, (Var.t, lm_entry list) Hashtbl.t) Hashtbl.t = Hashtbl.create (module Tid)

let clear () = Hashtbl.clear table; Hashtbl.clear head_table

let clear_head (_head : Tid.t) = Hashtbl.clear table; Hashtbl.clear head_table
let clear_head_and_descendants (h:Tid.t) = clear_head h

let add_smaller_dist (entries : lm_entry list) (entry : lm_entry) : lm_entry list =
  match List.find entries ~f:(fun e ->
      Word.equal e.bound entry.bound
      && Bool.equal e.is_upper entry.is_upper) with
  | None -> entry :: entries
  | Some existing ->
    let keep =
      match existing.dist, entry.dist with
      | None, _ | _, None -> true
      | Some d1, Some d2 -> d2 < d1
    in
    if keep then entry :: List.filter entries ~f:(fun e -> not (
      Word.equal e.bound entry.bound
      && Bool.equal e.is_upper entry.is_upper)) else entries

let record_landmark_for_head ~(head:Tid.t) (v : var) ~(bound : Word.t) ~(is_upper : bool) ~(dist : int) : unit =
  let entry = { bound; is_upper; dist = Some dist } in
  let tbl =
    match Hashtbl.find head_table head with
    | Some m -> m
    | None -> let m = Hashtbl.create (module Var) in Hashtbl.set head_table ~key:head ~data:m; m
  in
  let key = Var.base v in
  let cur = Hashtbl.find tbl key |> Option.value ~default:[] in
  let next = add_smaller_dist cur entry in
  Hashtbl.set tbl ~key ~data:next;
  let cur2 = Hashtbl.find table key |> Option.value ~default:[] in
  let next2 = add_smaller_dist cur2 entry in
  Hashtbl.set table ~key ~data:next2

let record_landmark (v : var) ~(bound : Word.t) ~(is_upper : bool) ~(dist : int) : unit =
  (match !current_head with
  | Some h -> record_landmark_for_head ~head:h v ~bound ~is_upper ~dist
  | None ->
    let entry = { bound; is_upper; dist = Some dist } in
    let key = Var.base v in
    let cur = Hashtbl.find table key |> Option.value ~default:[] in
    let next = add_smaller_dist cur entry in
    Hashtbl.set table ~key ~data:next)

let bounds_for (v : var) : Word.t list =
  let entries = Hashtbl.find table (Var.base v) |> Option.value ~default:[] in
  List.sort ~compare:Word.compare (List.map entries ~f:(fun e -> e.bound))

let bounds_for_head (head : Tid.t) (v : var) : Word.t list =
  match Hashtbl.find head_table head with
  | None -> []
  | Some m ->
    let entries = Hashtbl.find m (Var.base v) |> Option.value ~default:[] in
    List.sort ~compare:Word.compare (List.map entries ~f:(fun e -> e.bound))

let entries_for_head (head : Tid.t) (v : var) : lm_entry list =
  match Hashtbl.find head_table head with
  | None -> []
  | Some m -> Hashtbl.find m (Var.base v) |> Option.value ~default:[]

let entries_for (v : var) : lm_entry list =
  Hashtbl.find table (Var.base v) |> Option.value ~default:[]

(* Compatibility shims for the spec's naming — all map to the same table. *)
let heads_of_wto _ = Tid.Set.empty

let observe_unsat _ _ = ()

(* Acquisition helper: called from meet_var when meet is empty. Records the
   disabled boundary (the cstr's extremum outside p) as a landmark for the
   current var. *)
let observe_unsat_var (v : var) ~(p : Cbat_clp_set_composite.t) ~(cstr : Cbat_clp_set_composite.t) : unit =
  if Cbat_clp_set_composite.bitwidth p <> Cbat_clp_set_composite.bitwidth cstr then ()
  else
    let m = Cbat_clp_set_composite.meet p cstr in
    if not (Cbat_clp_set_composite.is_bottom m) then ()
    else
      match Cbat_clp_set_composite.min_elem p, Cbat_clp_set_composite.max_elem p,
            Cbat_clp_set_composite.min_elem cstr, Cbat_clp_set_composite.max_elem cstr with
      | Some p_min, Some p_max, Some c_min, Some c_max ->
        if Word.(<) p_max c_min then begin
          let d = distance_words p_max c_min in
          record_landmark v ~bound:c_min ~is_upper:false ~dist:(cap_distance d)
        end else if Word.(>) p_min c_max then begin
          let d = distance_words c_max p_min in
          record_landmark v ~bound:c_max ~is_upper:true ~dist:(cap_distance d)
        end else ()
      | _ -> ()

let lm_calc_steps _ = `Inf

let lm_advance (_head : Tid.t) = ()

(* Distance-capped helpers for spec v2: cap at 2^40 *)
let cap_distance (d : int) : int = min d (1 lsl 40)

