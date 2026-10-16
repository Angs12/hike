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
  let head_to_blocks : (Tid.t, Tid.Set.t) Hashtbl.t = Hashtbl.create (module Tid) in
  let block_to_head : (Tid.t, Tid.t) Hashtbl.t = Hashtbl.create (module Tid) in
  let next = ref 0 in
  let pos_of = ref Tid.Map.empty in
  let place (t : Tid.t) : unit =
    pos_of := Core.Map.set !pos_of ~key:t ~data:!next;
    incr next
  in
  (* Pre-order walk with the innermost enclosing head; returns the
     comps' blocks in order. *)
  let rec walk (enclosing : Tid.t option) (comps : comp list) : Tid.t list =
    List.concat_map comps ~f:(function
        | Vertex v ->
          place v;
          Option.iter enclosing ~f:(fun h ->
              Hashtbl.set block_to_head ~key:v ~data:h);
          [ v ]
        | SCC (h, inner) ->
          place h;
          Hashtbl.set block_to_head ~key:h ~data:h;
          Hashtbl.set head_to_blocks ~key:h ~data:Tid.Set.empty;
          let blocks = h :: walk (Some h) inner in
          Hashtbl.set head_to_blocks ~key:h ~data:(Tid.Set.of_list blocks);
          blocks)
  in
  ignore (walk None cs : Tid.t list);
  let heads = Tid.Set.of_list (Hashtbl.keys head_to_blocks) in
  { heads; head_to_blocks; block_to_head; pos_of = !pos_of }

(* Kosaraju SCC over any ordered key: the block-graph partition and the
   widening-need var graph both call it (one interface, two adapters). *)
module Scc (K : Hashtbl.Key) =
struct
  let partition (nodes : K.t list) (succ : K.t -> K.t list)
      (pred : K.t -> K.t list) : K.t list list =
    (* Membership is hashed, not scanned — the DFS visits are O(V.E)
       total, not O(V^2.E).  Visit order is unchanged. *)
    let in_nodes = Hashtbl.create (module K) in
    List.iter nodes ~f:(fun n -> Hashtbl.set in_nodes ~key:n ~data:true);
    let visited = Hashtbl.create (module K) in
    let order = ref [] in
    let rec dfs1 (n : K.t) : unit =
      if not (Hashtbl.mem visited n) then begin
        Hashtbl.set visited ~key:n ~data:true;
        List.iter (succ n) ~f:(fun m ->
            if Hashtbl.mem in_nodes m then dfs1 m);
        order := n :: !order
      end
    in
    List.iter nodes ~f:dfs1;
    let visited2 = Hashtbl.create (module K) in
    let comps = ref [] in
    List.iter !order ~f:(fun n ->
        if not (Hashtbl.mem visited2 n) then begin
          let cur = ref [] in
          let rec dfs2 (x : K.t) : unit =
            if not (Hashtbl.mem visited2 x) then begin
              Hashtbl.set visited2 ~key:x ~data:true;
              cur := x :: !cur;
              List.iter (pred x) ~f:(fun p ->
                  if Hashtbl.mem in_nodes p then dfs2 p)
            end
          in
          dfs2 n;
          comps := !cur :: !comps
        end);
    !comps
end

module Tid_scc = Scc (Tid)

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
