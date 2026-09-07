(* Simon & King landmark widening. Empty meets acquire landmarks; heads extrapolate toward them. *)

open Bap.Std
open Core_kernel

(* Per-(var, bound, is_upper) entry; smaller distance wins. *)
type lm_entry = {
  bound : Cbat_word.t;
  is_upper : bool;
  mutable dist : int option;   (* current distance *)
  mutable dist_p : int option;  (* previous distance *)
}

let cap = 1 lsl 40
let cap_distance (d : int) : int = min d cap
let distance_words (a : Cbat_word.t) (b : Cbat_word.t) : int =
  let diff = Cbat_word.sub b a in
  try Cbat_word.to_int_exn diff with _ -> cap
  (* Cap unrepresentable distances. *)

(* Per-head landmark table. *)

(* Head currently widened; None outside a cycle. *)
let widening_at_head : Tid.t option ref = ref None

(* Head to landmark list. *)
let lm_env : (Tid.t, lm_entry list) Hashtbl.t = Hashtbl.create (module Tid)

let clear () = Hashtbl.clear lm_env

(* Drop entries of [h] and its SCC. *)
let clear_head (h : Tid.t) (blocks : Tid.Set.t) : unit =
  Hashtbl.remove lm_env h;
  Core.Set.iter blocks ~f:(fun btid -> Hashtbl.remove lm_env btid)

let add_smaller_dist (entries : lm_entry list) (entry : lm_entry) : lm_entry list =
  match List.find entries ~f:(fun e ->
      Cbat_word.equal e.bound entry.bound
      && Bool.equal e.is_upper entry.is_upper) with
  | None -> entry :: entries
  | Some existing ->
    let keep =
      match existing.dist, entry.dist with
      | None, _ | _, None -> true
      | Some d1, Some d2 -> d2 < d1
    in
    (* Preserve [dist_p]; only [lm_advance] rotates history. *)
    if keep then
      { entry with dist_p = existing.dist_p }
      :: List.filter entries ~f:(fun e -> not (
        Cbat_word.equal e.bound entry.bound
        && Bool.equal e.is_upper entry.is_upper))
    else entries

(* Counts acquisitions since the last reset. *)
let fired_count : int ref = ref 0
let start_fired_latch () : int = !fired_count
let end_fired_latch (base : int) : bool =
  let fired = !fired_count > base in
  fired_count := base;
  fired

let record_landmark_for_head ~(head:Tid.t) (v : var) ~(bound : Cbat_word.t) ~(is_upper : bool) ~(dist : int) : unit =
  (* Bumped on every acquisition. *)
  fired_count := !fired_count + 1;
  let entry = { bound; is_upper; dist = Some dist; dist_p = None } in
  let cur = Hashtbl.find lm_env head |> Option.value ~default:[] in
  let next = add_smaller_dist cur entry in
  Hashtbl.set lm_env ~key:head ~data:next

(* Entries recorded for [head]. *)
let entries_for_head (head : Tid.t) (_v : var) : lm_entry list =
  Hashtbl.find lm_env head |> Option.value ~default:[]

(* Record an empty meet's disabled boundary at the enclosing head. *)
let observe_unsat_var (v : var) ~(p : Cbat_clp_set_composite.t) ~(cstr : Cbat_clp_set_composite.t) : unit =
  if Cbat_clp_set_composite.bitwidth p <> Cbat_clp_set_composite.bitwidth cstr then ()
  else
    let m = Cbat_clp_set_composite.meet p cstr in
    if not (Cbat_clp_set_composite.is_bottom m) then ()
    else
      match !widening_at_head,
            Cbat_clp_set_composite.min_elem p, Cbat_clp_set_composite.max_elem p,
            Cbat_clp_set_composite.min_elem cstr, Cbat_clp_set_composite.max_elem cstr with
      | None, _, _, _, _ ->
        (* Outside a cycle: no-op. *)
        ()
      | Some h, Some p_min, Some p_max, Some c_min, Some c_max ->
        if Cbat_word.(<) p_max c_min then begin
          (* Set below the boundary: upper landmark. *)
          let d = distance_words p_max c_min in
          record_landmark_for_head ~head:h v ~bound:c_min ~is_upper:true ~dist:(cap_distance d)
        end else if Cbat_word.(>) p_min c_max then begin
          (* Set above the boundary: lower landmark. *)
          let d = distance_words c_max p_min in
          record_landmark_for_head ~head:h v ~bound:c_max ~is_upper:false ~dist:(cap_distance d)
        end else ()
      | Some _, _, _, _, _ -> ()

(* Steps until the closest landmark; Zero needs another measurement, Inf widens. *)
let lm_calc_steps (h : Tid.t) : [> `Zero | `Finite of int | `Inf] =
  match Hashtbl.find lm_env h with
  | None -> `Inf
  | Some lst ->
    let has_zero = List.exists lst ~f:(fun e -> Option.is_none e.dist_p) in
    if has_zero then `Zero
    else
      let finite =
        List.filter_map lst ~f:(fun e ->
          match e.dist_p, e.dist with
          | Some dp, Some dc when dp > dc -> Some (dc / (dp - dc))
          | _ -> None)
      in
      if List.is_empty finite then `Inf
      else `Finite (List.min_elt finite ~compare:Int.compare |> Option.value_exn)

(* Commit current distances as previous. *)
let lm_advance (h : Tid.t) : unit =
  match Hashtbl.find lm_env h with
  | None -> ()
  | Some lst ->
    List.iter lst ~f:(fun entry ->
      entry.dist_p <- entry.dist;
      entry.dist <- None)




(* Extrapolate bounds toward landmarks; clamp at landmark and current bound. *)
let translate_to ~(steps : int) (data_old : Cbat_clp_set_composite.t)
    (data_new : Cbat_clp_set_composite.t)
    (entries : lm_entry list) : Cbat_clp_set_composite.t =
  let width = Cbat_clp_set_composite.bitwidth data_old in
  if width <> Cbat_clp_set_composite.bitwidth data_new then data_new
  else begin
    (* Growth per traversal times steps, clamped at landmark and bound. *)
    let cap = 1 lsl 40 in
    let delta_of (e : lm_entry) : int =
      match e.dist with
      | Some dc ->
        let g = match e.dist_p with Some dp when dp > dc -> dp - dc | _ -> 0 in
        let d = g * steps in
        if d > cap then cap else d
      | None -> 0
    in
    let lo_base = match Cbat_clp_set_composite.min_elem data_new with Some w -> w | None -> Cbat_word.zero width in
    let hi_base = match Cbat_clp_set_composite.max_elem data_new with Some w -> w | None -> Cbat_word.zero width in
    let extrap_lo =
      let lo' = List.filter entries ~f:(fun e -> not e.is_upper) in
      match lo' with
      | [] -> lo_base
      | _ ->
        let candidates = List.filter_map lo' ~f:(fun e ->
            let v = Cbat_word.sub lo_base (Cbat_word.of_int ~width (delta_of e)) in
            let v = if Cbat_word.compare v lo_base > 0 then lo_base else v in
            let v = if Cbat_word.compare v e.bound < 0 then e.bound else v in
            let v = if Cbat_word.compare v lo_base > 0 then lo_base else v in
            Some v)
        in
        List.fold candidates ~init:lo_base ~f:(fun acc v ->
            if Cbat_word.compare v acc < 0 then v else acc)
    in
    let extrap_hi =
      let hi' = List.filter entries ~f:(fun e -> e.is_upper) in
      match hi' with
      | [] -> hi_base
      | _ ->
        let candidates = List.filter_map hi' ~f:(fun e ->
            let v = Cbat_word.add hi_base (Cbat_word.of_int ~width (delta_of e)) in
            let v =
              if Cbat_word.compare v hi_base < 0 then
                (* Overflow saturates. *)
                Cbat_word.ones width
              else v in
            let v = if Cbat_word.compare v e.bound > 0 then e.bound else v in
            let v = if Cbat_word.compare v hi_base < 0 then hi_base else v in
            Some v)
        in
        List.fold candidates ~init:hi_base ~f:(fun acc v ->
            if Cbat_word.compare v acc > 0 then v else acc)
    in
    if Cbat_word.compare extrap_lo extrap_hi > 0 then data_new
    else Cbat_clp_set_composite.of_clp (Cbat_clp.interval ~width extrap_lo extrap_hi)
  end
