(* Landmark-directed widening — Simon & King "Widening Polyhedra with Landmarks" (APLAS 2006)

   v1: dynamic rung extensions — landmarks are extra thresholds.
   Faithful port will later replace this with Listing 4 extrapolation, but v1
   already makes LM F1 exact (K+1) and keeps the threshold ladder for other widths.

   API matches the spec's issues 01-05 so later wiring can be swapped without churn.
*)

open Bap.Std
open Core_kernel

(* per-(var, bound, is_upper) entry; smaller distance wins (updateLandmark) *)
type lm_entry = {
  bound : Word.t;
  is_upper : bool;
  mutable dist : int option;   (* dist_c — the current-iteration distance *)
  mutable dist_p : int option;  (* dist_p — the previous-iteration distance *)
}

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

(* [widening_at_head]: the WTO SCC head whose widening point is currently
   being processed; bound by [cbat_vsa.process_vertex] around the block
   denotation so that [observe_unsat_var] attributes landmarks to the
   innermost enclosing cycle. None = acquisition outside any WTO cycle,
   which is a sound no-op. *)
let widening_at_head : Tid.t option ref = ref None

(* [lm_env] — head -> landmark list, the per-cycle landmark table from
   Simon & King §4 (a landmark is a (var_base, bound, is_upper, dist) tuple
   recording the disabled-boundary distance observed on the taken edge). *)
let lm_env : (Tid.t, lm_entry list) Hashtbl.t = Hashtbl.create (module Tid)

let is_lm_sub : bool ref = ref false
let head_table : (Tid.t, (Var.t, lm_entry list) Hashtbl.t) Hashtbl.t = Hashtbl.create (module Tid)

let clear () = Hashtbl.clear table; Hashtbl.clear head_table

(* [clear_head h blocks]: drop the landmark tables for head [h] AND every
   block in [blocks] (the head's full SCC — its inner-SCC members and
   any strict descendants of [h] in the WTO tree, per spec Q9). After
   consumption at [h], the inner-SCC landmarks are obsolete: Bourdoncle's
   WTO order is "inner before outer," so any inner cycle has already
   been stabilized by the time [h]'s widening fires, and its recorded
   measurements would be re-fired as the second measurement of [h]'s
   landmark table if not cleared. Called from the widening-point
   transition in [cbat_vsa.process_vertex]. *)
let clear_head (h : Tid.t) (blocks : Tid.Set.t) : unit =
  Hashtbl.remove head_table h;
  Hashtbl.remove lm_env h;
  Core.Set.iter blocks ~f:(fun btid ->
    Hashtbl.remove head_table btid;
    Hashtbl.remove lm_env btid)

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
    (* dist_p (history) is preserved by [add_smaller_dist] — only [lm_advance] rotates it *)
    (* dist_p stays whatever it was — add_smaller_dist never resets history *)
    if keep then entry :: List.filter entries ~f:(fun e -> not (
      Word.equal e.bound entry.bound
      && Bool.equal e.is_upper entry.is_upper)) else entries

let record_landmark_for_head ~(head:Tid.t) (v : var) ~(bound : Word.t) ~(is_upper : bool) ~(dist : int) : unit =
  let entry = { bound; is_upper; dist = Some dist; dist_p = None } in
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
  (match !widening_at_head with
  | Some h -> record_landmark_for_head ~head:h v ~bound ~is_upper ~dist
  | None ->
    let entry = { bound; is_upper; dist = Some dist; dist_p = None } in
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

(* Compatibility shims for the spec's naming. *)
let heads_of_wto _ = Tid.Set.empty

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

(* [lm_calc_steps h]: Listing 3 — return Zero (a landmark still has no
   second measurement), Finite n (the minimum over landmarks of
   floor(dist_c / (dist_p - dist_c))), or Inf (no landmark has two
   measurements). *)
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

(* [lm_advance h]: Listing 2 — commit the current distance as the previous
   ([dist_p := dist_c]) and reset [dist_c] to None so the next acquisition
   starts a fresh first measurement. *)
let lm_advance (h : Tid.t) : unit =
  match Hashtbl.find lm_env h with
  | None -> ()
  | Some lst ->
    List.iter lst ~f:(fun entry ->
      entry.dist_p <- entry.dist;
      entry.dist <- None)




(* [translate_to ~steps data_old data_new entries]: Listing 4 landmark
   consumption — for each non-redundant bound (e <= c) of data_old, compute
   c' = min(data_old ∪ data_new, e <= c); if c' > c keep (stable), else
   translate outward by dist*steps onto the word grid; overflow -> the
   infinite arm (clamp to word_max). The result is the join of the lo- and
   hi- extrapolation (when both have entries) or a single translate; if the
   two extrapolations cross (lo > hi) we fall back to plain widening. *)
let translate_to ~(steps : int) (data_old : Cbat_clp_set_composite.t)
    (data_new : Cbat_clp_set_composite.t)
    (entries : lm_entry list) : Cbat_clp_set_composite.t =
  let width = Cbat_clp_set_composite.bitwidth data_old in
  if width <> Cbat_clp_set_composite.bitwidth data_new then data_new
  else begin
    let lo_base = match Cbat_clp_set_composite.min_elem data_new with Some w -> w | None -> Word.zero width in
    let hi_base = match Cbat_clp_set_composite.max_elem data_new with Some w -> w | None -> Word.zero width in
    let extrap_lo =
      let lo' = List.filter entries ~f:(fun e -> not e.is_upper) in
      match lo' with
      | [] -> lo_base
      | _ ->
        let min_dist = List.fold lo' ~init:(1 lsl 40)
          ~f:(fun acc e -> match e.dist with Some d -> min acc d | None -> acc) in
        let delta = Word.mul (Word.of_int ~width min_dist) (Word.of_int ~width steps) in
        if Word.compare delta (Word.zero width) = 0 then lo_base
        else
          let v = Word.sub lo_base delta in
          if Word.compare v lo_base > 0 then lo_base else v
    in
    let extrap_hi =
      let hi' = List.filter entries ~f:(fun e -> e.is_upper) in
      match hi' with
      | [] -> hi_base
      | _ ->
        let max_dist = List.fold hi' ~init:0
          ~f:(fun acc e -> match e.dist with Some d -> max acc d | None -> acc) in
        let delta = Word.mul (Word.of_int ~width max_dist) (Word.of_int ~width steps) in
        let v = Word.add hi_base delta in
        if Word.compare v hi_base < 0 then
          (* overflow -> infinite arm (Listing 4): word_max *)
          Word.ones width
        else v
    in
    let lo = if Word.compare extrap_lo lo_base > 0 then extrap_lo else lo_base in
    let hi = if Word.compare extrap_hi hi_base < 0 then extrap_hi else hi_base in
    if Word.compare lo hi > 0 then data_new
    else Cbat_clp_set_composite.of_clp (Cbat_clp.interval ~width lo hi)
  end
