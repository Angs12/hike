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

(* Bourdoncle weak topological ordering over plain accessors. Heads are the minimal widening-point set; swapped accessors build the reversed ordering. *)

open Core_kernel
open Bap.Std

type comp =
  | Vertex of Tid.t
  | SCC of Tid.t * comp list

let rec flatten_comps (cs : comp list) : Tid.t list =
  List.concat_map cs ~f:(function
      | Vertex v -> [v]
      | SCC (h, inner) -> h :: flatten_comps inner)

let rec heads_of_comps (cs : comp list) : Tid.Set.t =
  List.fold cs ~init:Tid.Set.empty ~f:(fun acc -> function
      | Vertex _ -> acc
      | SCC (h, inner) ->
        let acc = Core.Set.add acc h in
        Core.Set.union acc (heads_of_comps inner))

(* Recursive SCC partition. *)
let scc_partition
    (nodes : Tid.t list)
    (succ : Tid.t -> Tid.t list)
    (pred : Tid.t -> Tid.t list)
  : Tid.t list list =
  let node_set = Tid.Set.of_list nodes in
  let visited = ref Tid.Set.empty in
  let order = ref [] in
  let rec dfs1 (n : Tid.t) : unit =
    if not (Core.Set.mem !visited n) then begin
      visited := Core.Set.add !visited n;
      List.iter (succ n) ~f:(fun m ->
          if Core.Set.mem node_set m then dfs1 m);
      order := n :: !order
    end
  in
  List.iter nodes ~f:dfs1;
  let visited2 = ref Tid.Set.empty in
  let comps = ref [] in
  List.iter !order ~f:(fun n ->
      if not (Core.Set.mem !visited2 n) then begin
        let cur = ref [] in
        let rec dfs2 (x : Tid.t) : unit =
          if not (Core.Set.mem !visited2 x) then begin
            visited2 := Core.Set.add !visited2 x;
            cur := x :: !cur;
            List.iter (pred x) ~f:(fun p ->
                if Core.Set.mem node_set p then dfs2 p)
          end
        in
        dfs2 n;
        comps := !cur :: !comps
      end);
  !comps

(* WTO over plain accessors. *)
let wto ~(nodes : Tid.t list) ~(succ : Tid.t -> Tid.t list)
    ~(pred : Tid.t -> Tid.t list) : comp list =
  if List.is_empty nodes then [] else
  let rpo_index : (Tid.t, int) Hashtbl.t = Hashtbl.create (module Tid) in
  begin
    let visited = ref Tid.Set.empty in
    let order = ref [] in
    let rec dfs (n : Tid.t) : unit =
      if not (Core.Set.mem !visited n) then begin
        visited := Core.Set.add !visited n;
        List.iter (succ n) ~f:dfs;
        order := n :: !order
      end
    in
    List.iter nodes ~f:dfs;
    List.iteri !order ~f:(fun i n -> Hashtbl.set rpo_index ~key:n ~data:i)
  end;
  let get_rpo (n : Tid.t) : int =
    Hashtbl.find rpo_index n |> Option.value ~default:Int.max_value in
  let has_self_loop (n : Tid.t) : bool =
    List.mem (succ n) n ~equal:Tid.equal in
  let rec wto_rec (nodes : Tid.t list) : comp list =
    if List.is_empty nodes then [] else
      let node_set = Tid.Set.of_list nodes in
      let succ (n : Tid.t) : Tid.t list =
        List.filter (succ n) ~f:(fun m -> Core.Set.mem node_set m) in
      let pred (n : Tid.t) : Tid.t list =
        List.filter (pred n) ~f:(fun m -> Core.Set.mem node_set m) in
      let sccs = scc_partition nodes succ pred in
      let sccs_sorted =
        List.sort sccs ~compare:(fun a b ->
            let ma = List.map a ~f:get_rpo |> List.min_elt ~compare:Int.compare |> Option.value ~default:Int.max_value in
            let mb = List.map b ~f:get_rpo |> List.min_elt ~compare:Int.compare |> Option.value ~default:Int.max_value in
            Int.compare ma mb) in
      List.concat_map sccs_sorted ~f:(fun scc ->
          match scc with
          | [v] when not (has_self_loop v) -> [Vertex v]
          | _ ->
            let head =
              List.min_elt scc ~compare:(fun a b -> Int.compare (get_rpo a) (get_rpo b))
              |> Option.value_exn in
            let rest = List.filter scc ~f:(fun n -> not (Tid.equal n head)) in
            let inner = wto_rec rest in
            [SCC (head, inner)])
  in
  wto_rec nodes
