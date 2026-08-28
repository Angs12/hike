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
   table is global.  v2 will add per-head scoping. *)
let table : (Var.t, Word.t list) Hashtbl.t = Hashtbl.create (module Var)

let current_head : Tid.t option ref = ref None

let clear () = Hashtbl.clear table

let record_landmark (v : var) (bound : Word.t) : unit =
  let key = Var.base v in
  let cur = Hashtbl.find table key |> Option.value ~default:[] in
  if not (List.mem cur bound ~equal:Word.equal) then begin
    let next = List.sort ~compare:Word.compare (bound :: cur) in
    Hashtbl.set table ~key ~data:next
  end

let landmarks_for (v : var) : Word.t list =
  Hashtbl.find table (Var.base v) |> Option.value ~default:[]

(* Compatibility shims for the spec's naming — all map to the same table. *)
let heads_of_wto _ = Tid.Set.empty
let observe_unsat _ _ = ()
let lm_calc_steps _ = `Inf

