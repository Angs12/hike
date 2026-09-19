(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

(* The engine's dispatch graph: the CFG plus the Resolved dispatches'
   extra successor edges.  One succs/preds pair serves the WTO, the
   worklist, and the per-block predecessor lists. *)

open Core
open Bap.Std
open Graphlib.Std

type t = {
  succs : tid -> tid list;
  preds : tid -> tid list;
}

(* The resolved dispatches' extra successor edges, keyed by BLOCK: the
   union of its jmps' target sets, filtered to engine blocks. *)
let extras_of_sub ~(blocks : Tid.Set.t)
    (resolved : Tid.Set.t Tid.Map.t) (sub : sub term) :
    Tid.Set.t Tid.Map.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
      let es =
        Term.enum jmp_t b
        |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc j ->
            match Core.Map.find resolved (Term.tid j) with
            | Some ts -> Core.Set.union acc ts
            | None -> acc)
      in
      let es = Core.Set.filter es ~f:(fun t -> Core.Set.mem blocks t) in
      if Core.Set.is_empty es then m
      else Core.Map.set m ~key:(Term.tid b) ~data:es)

let make ~(cfg : Graphs.Tid.t) ~(blocks : Tid.Set.t)
    (resolved : Tid.Set.t Tid.Map.t) (sub : sub term) : t =
  let extras = extras_of_sub ~blocks resolved sub in
  let succs (v : tid) : tid list =
    let base = Graphs.Tid.Node.succs v cfg |> Seq.to_list in
    match Core.Map.find extras v with
    | None -> base
    | Some es ->
      Base.List.fold (Core.Set.to_list es) ~init:base ~f:(fun acc t ->
          if Base.List.mem acc t ~equal:Tid.equal then acc else t :: acc)
  in
  let preds =
    Graphs.Tid.nodes cfg
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m v ->
        Core.Map.set m ~key:v
          ~data:(Graphs.Tid.Node.preds v cfg |> Seq.to_list))
  in
  let preds =
    Core.Map.fold extras ~init:preds
      ~f:(fun ~key:v ~data:es acc ->
        Core.Set.fold es ~init:acc ~f:(fun acc w ->
            let ps = Option.value (Core.Map.find acc w) ~default:[] in
            if Base.List.mem ps v ~equal:Tid.equal then acc
            else Core.Map.set acc ~key:w ~data:(v :: ps)))
  in
  { succs;
    preds = fun v -> Option.value ~default:[] (Core.Map.find preds v) }
