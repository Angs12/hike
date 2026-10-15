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

open Core
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

(* The driver's views of one ordering, built in a single pass: the head
   set, each head's member blocks, each block's innermost head, and the
   WTO position index. *)
type summary = {
  heads : Tid.Set.t;
  head_to_blocks : (Tid.t, Tid.Set.t) Hashtbl.t;
  block_to_head : (Tid.t, Tid.t) Hashtbl.t;
  pos_of : int Tid.Map.t;
}

let summary (cs : comp list) : summary =
  let heads = heads_of_comps cs in
  let head_to_blocks : (Tid.t, Tid.Set.t) Hashtbl.t = Hashtbl.create (module Tid) in
  let rec collect comps =
    List.iter comps ~f:(function
        | Vertex _ -> ()
        | SCC (h, inner) ->
          let blocks = Tid.Set.of_list (h :: flatten_comps inner) in
          Hashtbl.set head_to_blocks ~key:h ~data:blocks;
          collect inner)
  in
  collect cs;
  let block_to_head : (Tid.t, Tid.t) Hashtbl.t = Hashtbl.create (module Tid) in
  Hashtbl.iteri head_to_blocks ~f:(fun ~key:h ~data:blocks ->
      Core.Set.iter blocks ~f:(fun btid ->
          match Hashtbl.find block_to_head btid with
          | None -> Hashtbl.set block_to_head ~key:btid ~data:h
          | Some existing ->
            (* Innermost wins. *)
            let existing_set = Hashtbl.find_exn head_to_blocks existing in
            if Core.Set.length blocks < Core.Set.length existing_set then
              Hashtbl.set block_to_head ~key:btid ~data:h));
  let pos_of =
    List.mapi (flatten_comps cs) ~f:(fun i t -> (t, i))
    |> List.fold ~init:Tid.Map.empty ~f:(fun m (t, i) ->
        Core.Map.set m ~key:t ~data:i) in
  { heads; head_to_blocks; block_to_head; pos_of }

(* Kosaraju SCC over any ordered key: the block-graph partition and the
   widening-need var graph both call it (one interface, two adapters). *)
module Scc (K : sig
    type t
  end) =
struct
  let partition (nodes : K.t list) (succ : K.t -> K.t list)
      (pred : K.t -> K.t list) : K.t list list =
    (* Membership is hashed, not scanned — the DFS visits are O(V.E)
       total, not O(V^2.E).  Visit order is unchanged. *)
    let in_nodes = Stdlib.Hashtbl.create 64 in
    List.iter nodes ~f:(fun n -> Stdlib.Hashtbl.replace in_nodes n true);
    let visited = Stdlib.Hashtbl.create 64 in
    let order = ref [] in
    let rec dfs1 (n : K.t) : unit =
      if not (Stdlib.Hashtbl.mem visited n) then begin
        Stdlib.Hashtbl.replace visited n true;
        List.iter (succ n) ~f:(fun m ->
            if Stdlib.Hashtbl.mem in_nodes m then dfs1 m);
        order := n :: !order
      end
    in
    List.iter nodes ~f:dfs1;
    let visited2 = Stdlib.Hashtbl.create 64 in
    let comps = ref [] in
    List.iter !order ~f:(fun n ->
        if not (Stdlib.Hashtbl.mem visited2 n) then begin
          let cur = ref [] in
          let rec dfs2 (x : K.t) : unit =
            if not (Stdlib.Hashtbl.mem visited2 x) then begin
              Stdlib.Hashtbl.replace visited2 x true;
              cur := x :: !cur;
              List.iter (pred x) ~f:(fun p ->
                  if Stdlib.Hashtbl.mem in_nodes p then dfs2 p)
            end
          in
          dfs2 n;
          comps := !cur :: !comps
        end);
    !comps
end

module Tid_scc = Scc (struct
    type t = Tid.t
  end)

(* WTO over plain accessors. *)
let wto ~(nodes : Tid.t list) ~(succ : Tid.t -> Tid.t list)
    ~(pred : Tid.t -> Tid.t list) : comp list =
  if List.is_empty nodes then [] else
  let rpo =
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
    !order
  in
  let has_self_loop (n : Tid.t) : bool =
    List.mem (succ n) n ~equal:Tid.equal in
  let rec wto_rec (nodes : Tid.t list) (rpo : Tid.t list) : comp list =
    if List.is_empty nodes then [] else
      let node_set = Tid.Set.of_list nodes in
      let succ (n : Tid.t) : Tid.t list =
        List.filter (succ n) ~f:(fun m -> Core.Set.mem node_set m) in
      let pred (n : Tid.t) : Tid.t list =
        List.filter (pred n) ~f:(fun m -> Core.Set.mem node_set m) in
      let sccs = Array.of_list (Tid_scc.partition nodes succ pred) in
      let owners = Hashtbl.create (module Tid) in
      Array.iteri sccs ~f:(fun i scc ->
          List.iter scc ~f:(fun n -> Hashtbl.set owners ~key:n ~data:i));
      let members = Array.create ~len:(Array.length sccs) [] in
      (* The RPO producer supplies both component order and each head:
         a component's first encountered member has its minimum RPO. *)
      let component_order =
        List.filter_map rpo ~f:(fun n ->
            match Hashtbl.find owners n with
            | None -> None
            | Some i ->
              let first = List.is_empty members.(i) in
              members.(i) <- n :: members.(i);
              Option.some_if first i)
      in
      List.concat_map component_order ~f:(fun i ->
          match List.rev members.(i) with
          | [v] when not (has_self_loop v) -> [Vertex v]
          | head :: ordered_rest ->
            let rest = List.filter sccs.(i) ~f:(fun n -> not (Tid.equal n head)) in
            let inner = wto_rec rest ordered_rest in
            [SCC (head, inner)]
          | [] -> assert false)
  in
  wto_rec nodes rpo
