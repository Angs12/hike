(* Landmark-directed widening — Simon & King "Widening Polyhedra with Landmarks" (APLAS 2006)

   v1: dynamic rung extensions — landmarks are extra thresholds.
   Faithful port will later replace this with Listing 4 extrapolation, but v1
   already makes LM F1 exact (K+1) and keeps the threshold ladder for other widths.

   API matches the spec's issues 01-05 so later wiring can be swapped without churn.
*)

open Bap.Std
open Core_kernel

(* Global landmark environment — per Var.base -> sorted deduped Word.t list.
   Head attribution is skipped in v1 (single-loop tests don't need it); the
   table is global.  v2 will add per-head scoping.  Spec v2 keeps the global
   table as the sound fallback (per-var disabled boundaries) while also
   exposing the per-head API. *)
let table : (Var.t, Word.t list) Hashtbl.t = Hashtbl.create (module Var)

let current_head : Tid.t option ref = ref None

(* spec v2 aliases *)
let current_lm_head : Tid.t option ref = current_head
let landmark_env : (Tid.t, (Var.t * Word.t * int * int option) list) Hashtbl.t ref =
  ref (Hashtbl.create (module Tid))

let is_lm_sub : bool ref = ref false
let head_table : (Tid.t, (Var.t, Word.t list) Hashtbl.t) Hashtbl.t = Hashtbl.create (module Tid)

let clear () = Hashtbl.clear table; Hashtbl.clear head_table

let clear_head (_head : Tid.t) = Hashtbl.clear table; Hashtbl.clear head_table
let clear_head_and_descendants (h:Tid.t) = clear_head h

let record_landmark_for_head ~(head:Tid.t) (v : var) (bound : Word.t) : unit =
  let tbl =
    match Hashtbl.find head_table head with
    | Some m -> m
    | None -> let m = Hashtbl.create (module Var) in Hashtbl.set head_table ~key:head ~data:m; m
  in
  let key = Var.base v in
  let cur = Hashtbl.find tbl key |> Option.value ~default:[] in
  if not (List.mem cur bound ~equal:Word.equal) then begin
    let next = List.sort ~compare:Word.compare (bound :: cur) in
    Hashtbl.set tbl ~key ~data:next
  end;
  (* also keep global for fallback *)
  let cur2 = Hashtbl.find table key |> Option.value ~default:[] in
  if not (List.mem cur2 bound ~equal:Word.equal) then begin
    let next2 = List.sort ~compare:Word.compare (bound :: cur2) in
    Hashtbl.set table ~key ~data:next2
  end

let record_landmark (v : var) (bound : Word.t) : unit =
  (match !current_head with
  | Some h -> record_landmark_for_head ~head:h v bound
  | None ->
    let key = Var.base v in
    let cur = Hashtbl.find table key |> Option.value ~default:[] in
    if not (List.mem cur bound ~equal:Word.equal) then begin
      let next = List.sort ~compare:Word.compare (bound :: cur) in
      Hashtbl.set table ~key ~data:next
    end)

let landmarks_for (v : var) : Word.t list =
  Hashtbl.find table (Var.base v) |> Option.value ~default:[]

let landmarks_for_head (head:Tid.t) (v:var) : Word.t list =
  match Hashtbl.find head_table head with
  | None -> []
  | Some m -> Hashtbl.find m (Var.base v) |> Option.value ~default:[]

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
        if Word.(<) p_max c_min then record_landmark v c_min
        else if Word.(>) p_min c_max then record_landmark v c_max
        else ()
      | _ -> ()

let lm_calc_steps _ = `Inf

let lm_advance (_head : Tid.t) = ()

(* Distance-capped helpers for spec v2: cap at 2^40 *)
let cap_distance (d : int) : int = min d (1 lsl 40)

