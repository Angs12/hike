(* WTO ordering pins.  One Alcotest group per assertion; each pin builds its
   own graph, so no state crosses pins. *)

open Bap.Std
open Bap_core_theory
open Hike_test.Harness
open Hike_test.Common
open Hike_test.Fixtures

module Cw = Cbat_vsa__Cbat_wto
module Dg = Cbat_vsa__Cbat_dispatch_graph

module Tid_scc = Cw.Scc (struct
    type t = Tid.t
    let compare = Tid.compare
  end)

(* Explicit graphs: a node list + an edge list; the accessors read the edge list. *)
let succs edges n =
  Base.List.filter_map edges ~f:(fun (u, v) -> if Tid.equal u n then Some v else None)

let preds edges n =
  Base.List.filter_map edges ~f:(fun (u, v) -> if Tid.equal v n then Some u else None)

let wto_of nodes edges = Cw.wto ~nodes ~succ:(succs edges) ~pred:(preds edges)

let rec members (c : Cw.comp) : Tid.t list =
  match c with
  | Cw.Vertex v -> [ v ]
  | Cw.SCC (h, inner) -> h :: Base.List.concat_map inner ~f:members

(* Every Cw.SCC component of the forest with its full member set. *)
let rec scc_comps (cs : Cw.comp list) : (Tid.t * Tid.t list) list =
  Base.List.concat_map cs ~f:(function
      | Cw.Vertex _ -> []
      | Cw.SCC (h, inner) -> (h, members (Cw.SCC (h, inner))) :: scc_comps inner)

let heads_set comps =
  Core.Set.of_list (module Tid) (Base.List.map (scc_comps comps) ~f:fst)

let comp_head (c : Cw.comp) : Tid.t option =
  match c with Cw.SCC (h, _) -> Some h | Cw.Vertex _ -> None

(* Is [n] on a cycle: reachable from itself through at least one edge. *)
let on_a_cycle edges n =
  let rec go visited = function
    | [] -> false
    | m :: rest ->
      if Tid.equal m n then true
      else if Core.Set.mem visited m then go visited rest
      else go (Core.Set.add visited m) (succs edges m @ rest)
  in
  go (Core.Set.singleton (module Tid) n) (succs edges n)

(* Flattened position of a vertex (the component-order pins). *)
let pos_of flat n =
  match Base.List.findi flat ~f:(fun _ m -> Tid.equal m n) with
  | Some (p, _) -> p
  | None -> failwith "WTO: vertex missing from the flattened order"

(* The graph SCCs that are cycles: more than one member, or a self-loop. *)
let gsccs_of nodes edges =
  Tid_scc.partition nodes (succs edges) (preds edges)
  |> Base.List.filter ~f:(fun c -> List.length c > 1 || on_a_cycle edges (Base.List.hd_exn c))
  |> Base.List.map ~f:(Core.Set.of_list (module Tid))

let wsccs_of comps =
  Base.List.map (scc_comps comps) ~f:(fun (_, ms) -> Core.Set.of_list (module Tid) ms)

(* The Bourdoncle battery over one graph: vertex coverage, heads are
   exactly cycle-bound widening points, every loop's Cw.SCC is one WTO
   component carrying a head.  Five pins per call; [setup] rebuilds the
   graph inside each closure. *)
let wto_battery_pins ~(ids : string list) ~(label : string)
    (setup : unit -> Tid.t list * (Tid.t * Tid.t) list) : unit Alcotest.test list =
  match ids with
  | [ i1; i2; i3; i4; i5 ] ->
    [
      pin i1 (label ^ ": every vertex appears exactly once in the flattened order")
        (fun () ->
          let nodes, edges = setup () in
          let comps = wto_of nodes edges in
          let flat = Cw.flatten_comps comps in
          check i1
            (List.length flat = List.length nodes
             && Core.Set.equal
                  (Core.Set.of_list (module Tid) flat)
                  (Core.Set.of_list (module Tid) nodes)));
      pin i2 (label ^ ": every head lies on a cycle (no spurious widening points)")
        (fun () ->
          let nodes, edges = setup () in
          let comps = wto_of nodes edges in
          let hs = heads_set comps in
          check i2 (Core.Set.for_all hs ~f:(on_a_cycle edges)));
      pin i3 (label ^ ": every nontrivial graph SCC is exactly one WTO component's member set")
        (fun () ->
          let nodes, edges = setup () in
          let comps = wto_of nodes edges in
          let gsccs = gsccs_of nodes edges in
          let wsccs = wsccs_of comps in
          check i3
            (Base.List.for_all gsccs ~f:(fun g -> Base.List.exists wsccs ~f:(Core.Set.equal g))));
      pin i4 (label ^ ": every nontrivial graph SCC contains one of the heads")
        (fun () ->
          let nodes, edges = setup () in
          let comps = wto_of nodes edges in
          let hs = heads_set comps in
          let gsccs = gsccs_of nodes edges in
          check i4
            (Base.List.for_all gsccs ~f:(fun ms ->
                 not (Core.Set.is_empty (Core.Set.inter ms hs)))));
      pin i5 (label ^ ": heads_of_comps is exactly the forest's head set")
        (fun () ->
          let nodes, edges = setup () in
          let comps = wto_of nodes edges in
          let hs = heads_set comps in
          check i5 (Core.Set.equal (Cw.heads_of_comps comps) hs));
    ]
  | _ -> failwith "wto_battery_pins expects five ids"

(* The integrated-shape graph: entry -> outer loop {h1 with inner loop {i}} ->
   second loop {l2} -> exit.  Returns the named vertices plus both renderings. *)
let wto_graph () =
  let e = Tid.create () and h1 = Tid.create () and iv = Tid.create () and j = Tid.create () in
  let k = Tid.create () and l2 = Tid.create () and b2 = Tid.create () and x = Tid.create () in
  let nodes = [ e; h1; iv; j; k; l2; b2; x ] in
  let edges =
    [ (e, h1); (h1, iv); (iv, j); (j, iv); (iv, k); (k, h1); (h1, l2); (l2, b2); (b2, l2); (l2, x) ]
  in
  (e, h1, iv, j, k, l2, b2, x, nodes, edges)

let wto_graph_setup () =
  let _, _, _, _, _, _, _, _, nodes, edges = wto_graph () in
  (nodes, edges)

(* Swapped accessors build the reversed ordering: the same battery over the
   reversed edge list. *)
let wto_graph_reversed_setup () =
  let _, _, _, _, _, _, _, _, nodes, edges = wto_graph () in
  (nodes, Base.List.map edges ~f:(fun (u, v) -> (v, u)))

(* The dispatch-graph adapter: a Resolved dispatch's extra edges ride
   the dispatching block's successors and mirror into the targets'
   predecessor lists. *)
let cfg_of (sub : sub term) : Graphs.Tid.t =
  Graphs.Tid.Node.remove Graphs.Tid.exit
    (Graphs.Tid.Node.remove Graphs.Tid.start (Sub.to_graph sub))

let mk_dg_dispatch () =
  let foreign = Tid.create () in
  let sub, tids =
    sub_of "dg_dispatch"
      [ [], [ (1, mk_goto) ];
        [], [ (3, mk_goto) ];
        [], [ (3, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let entry = tids.(0) and b1 = tids.(1) and b2 = tids.(2) in
  let blocks = Core.Set.of_list (module Tid) (Array.to_list tids) in
  let resolved =
    Core.Map.singleton (module Tid) (Term.tid (sub_jmp sub 0 0))
      (Core.Set.of_list (module Tid) [ b1; b2; foreign ])
  in
  let { Dg.succs; Dg.preds; Dg.gained_preds = _ } = Dg.make ~cfg:(cfg_of sub) ~blocks resolved sub in
  (sub, entry, b1, b2, foreign, blocks, succs, preds)

let mk_dg_loop () =
  let sub2, tids2 =
    sub_of "dg_loop"
      [ [], [ (1, mk_goto) ];
        [], [ (2, mk_goto) ];
        [], [ (3, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let l0 = tids2.(0) and l1 = tids2.(1) and l2 = tids2.(2) in
  let { Dg.succs = loop_succs; Dg.preds = loop_preds; Dg.gained_preds = _ } =
    Dg.make ~cfg:(cfg_of sub2)
      ~blocks:(Core.Set.of_list (module Tid) (Array.to_list tids2))
      (Core.Map.singleton (module Tid) (Term.tid (sub_jmp sub2 2 0))
         (Core.Set.singleton (module Tid) l0))
      sub2
  in
  (Array.to_list tids2, l0, l1, l2, loop_succs, loop_preds)

(* The completed dispatch's graph view: the guarded-goto series lives
   in the BIR, so the case edges ARE term edges — the engine's
   succs/preds read the rewrite's one-edge-per-target series. *)
let mk_rows_dispatch () =
  let sub, tids =
    sub_of "rows_dispatch"
      [ [],
        [ (1, fun t ->
              Jmp.create
                ~cond:(Bil.BinOp (Bil.EQ, Bil.Var (v64 "rows_sel"),
                        Bil.Int (Cbat_word.to_word (w64 0x1010))))
                (Goto (Direct t)));
          (2, mk_goto) ];
        [], [ (0, mk_ret) ];
        [], [ (0, mk_ret) ] ]
  in
  let entry = tids.(0) and b1 = tids.(1) and b2 = tids.(2) in
  let { Dg.succs; Dg.preds; Dg.gained_preds = _ } =
    Dg.make ~cfg:(cfg_of sub)
      ~blocks:(Core.Set.of_list (module Tid) (Array.to_list tids))
      Tid.Map.empty sub
  in
  (entry, b1, b2, succs, preds)

let tests : unit Alcotest.test list =
  [
    (* The accessor contracts over a hand-built forest. *)
    pin "WTO-01" "WTO-FLATTEN: all blocks, and heads precede their members"
      (fun () ->
        let a = Tid.create () in
        let h = Tid.create () in
        let b = Tid.create () in
        let i = Tid.create () in
        let c = Tid.create () in
        let d = Tid.create () in
        let hand =
          [ Cw.Vertex a; Cw.SCC (h, [ Cw.Vertex b; Cw.SCC (i, [ Cw.Vertex c ]) ]); Cw.Vertex d ]
        in
        check "WTO-01" (Base.List.equal Tid.equal (Cw.flatten_comps hand) [ a; h; b; i; c; d ]));
    pin "WTO-02" "WTO-HEADS: heads_of_comps reaches the innermost SCCs (vertices contribute none)"
      (fun () ->
        let a = Tid.create () in
        let h = Tid.create () in
        let b = Tid.create () in
        let i = Tid.create () in
        let c = Tid.create () in
        let d = Tid.create () in
        let hand =
          [ Cw.Vertex a; Cw.SCC (h, [ Cw.Vertex b; Cw.SCC (i, [ Cw.Vertex c ]) ]); Cw.Vertex d ]
        in
        check "WTO-02"
          (Core.Set.equal (Cw.heads_of_comps hand) (Core.Set.of_list (module Tid) [ h; i ])));

    (* Acyclic diamond: no heads, every vertex a plain component. *)
    pin "WTO-03" "WTO-ACYCLIC: an acyclic graph produces no heads"
      (fun () ->
        let n0 = Tid.create () and n1 = Tid.create () and n2 = Tid.create () and n3 = Tid.create () in
        let diamond_edges = [ (n0, n1); (n0, n2); (n1, n3); (n2, n3) ] in
        let dcomps = wto_of [ n0; n1; n2; n3 ] diamond_edges in
        check "WTO-03" (Core.Set.is_empty (Cw.heads_of_comps dcomps)));
    pin "WTO-04" "WTO-ACYCLIC: an acyclic graph's components are all vertices"
      (fun () ->
        let n0 = Tid.create () and n1 = Tid.create () and n2 = Tid.create () and n3 = Tid.create () in
        let diamond_edges = [ (n0, n1); (n0, n2); (n1, n3); (n2, n3) ] in
        let dcomps = wto_of [ n0; n1; n2; n3 ] diamond_edges in
        check "WTO-04" (Base.List.for_all dcomps ~f:(function Cw.Vertex _ -> true | Cw.SCC _ -> false)));

    (* Self-loop: the single vertex is its own head. *)
    pin "WTO-05" "WTO-SELF: a self-looping vertex heads its own SCC"
      (fun () ->
        let s = Tid.create () in
        let scomps = wto_of [ s ] [ (s, s) ] in
        check "WTO-05"
          (match scomps with
           | [ Cw.SCC (hd, inner) ] -> Tid.equal hd s && Core.List.is_empty inner
           | _ -> false));

    (* Two-node cycle: the head precedes its member (heads-in-component). *)
    pin "WTO-06" "WTO-CYCLE: one SCC headed by the cycle's entry"
      (fun () ->
        let ca = Tid.create () and cb = Tid.create () in
        let ccomps = wto_of [ ca; cb ] [ (ca, cb); (cb, ca) ] in
        check "WTO-06"
          (match ccomps with
           | [ Cw.SCC (hd, inner) ] ->
             Tid.equal hd ca && Base.List.equal Tid.equal (Cw.flatten_comps inner) [ cb ]
           | _ -> false));
    pin "WTO-07" "WTO-CYCLE: the flattened order puts the head first"
      (fun () ->
        let ca = Tid.create () and cb = Tid.create () in
        let ccomps = wto_of [ ca; cb ] [ (ca, cb); (cb, ca) ] in
        check "WTO-07" (Base.List.equal Tid.equal (Cw.flatten_comps ccomps) [ ca; cb ]));
  ]
  @ wto_battery_pins ~ids:[ "WTO-08"; "WTO-09"; "WTO-10"; "WTO-11"; "WTO-12" ]
      ~label:"WTO-GRAPH" wto_graph_setup
  @ [
      (* Integrated shape: pins the component structure and the traversal
         order: heads first, the inner loop stabilizes before the outer tail,
         sequential loops stay siblings in order. *)
      pin "WTO-13" "WTO-GRAPH: the heads are exactly the three loop heads"
        (fun () ->
          let _, h1, iv, _, _, l2, _, _, nodes, edges = wto_graph () in
          let comps = wto_of nodes edges in
          check "WTO-13"
            (Core.Set.equal
               (Cw.heads_of_comps comps)
               (Core.Set.of_list (module Tid) [ h1; iv; l2 ])));
      pin "WTO-14" "WTO-GRAPH: the inner loop's SCC is nested inside the outer loop's SCC"
        (fun () ->
          let _, h1, iv, _, _, _, _, _, nodes, edges = wto_graph () in
          let comps = wto_of nodes edges in
          check "WTO-14"
            (match
               Base.List.find_map comps ~f:(function
                   | Cw.SCC (h, inner) when Tid.equal h h1 -> Some inner
                   | _ -> None)
             with
             | Some inner ->
               Base.List.exists inner ~f:(fun ic ->
                   Option.is_some
                     (Base.Option.filter (comp_head ic) ~f:(fun h2 -> Tid.equal h2 iv)))
             | None -> false));
      pin "WTO-15" "WTO-GRAPH: heads first, then the inner body, then the outer tail, then the next loop"
        (fun () ->
          let e, h1, iv, j, k, l2, b2, x, nodes, edges = wto_graph () in
          let comps = wto_of nodes edges in
          check "WTO-15"
            (Base.List.equal Tid.equal (Cw.flatten_comps comps) [ e; h1; iv; j; k; l2; b2; x ]));
      pin "WTO-16" "WTO-GRAPH: the inner loop's members stabilize before the outer tail (inner-before-outer)"
        (fun () ->
          let _, _, iv, j, k, _, _, _, nodes, edges = wto_graph () in
          let comps = wto_of nodes edges in
          check "WTO-16"
            (let flat = Cw.flatten_comps comps in
             pos_of flat iv < pos_of flat k && pos_of flat j < pos_of flat k));
      pin "WTO-17" "WTO-GRAPH: sequential loops are sibling components in traversal order"
        (fun () ->
          let _, h1, _, _, _, l2, _, _, nodes, edges = wto_graph () in
          let comps = wto_of nodes edges in
          check "WTO-17"
            (let flat = Cw.flatten_comps comps in
             Option.is_some
               (Base.Option.filter
                  (Base.List.find_map (scc_comps comps) ~f:(fun (hd, ms) ->
                       if Tid.equal hd h1 then Some ms else None))
                  ~f:(fun ms ->
                    not (Base.List.exists ms ~f:(Tid.equal l2))
                    && pos_of flat h1 < pos_of flat l2))));
    ]
  @ wto_battery_pins ~ids:[ "WTO-18"; "WTO-19"; "WTO-20"; "WTO-21"; "WTO-22" ]
      ~label:"WTO-REVERSED" wto_graph_reversed_setup
  @ [
      (* The Kosaraju partition underneath: exact components, disjoint. *)
      pin "WTO-23" "WTO-SCC: the partition isolates the cycle and the singleton"
        (fun () ->
          let module Int_scc = Cw.Scc (struct
              type t = int
              let compare = compare
            end) in
          let iparts =
            Int_scc.partition [ 1; 2; 3 ]
              (fun n -> if n = 1 then [ 2 ] else if n = 2 then [ 1 ] else [])
              (fun n -> if n = 1 then [ 2 ] else if n = 2 then [ 1 ] else [])
          in
          check "WTO-23"
            (let norm = Base.List.map iparts ~f:(fun l -> Base.List.sort ~compare:Core.Int.compare l) in
             Base.List.equal (Base.List.equal Core.Int.equal) norm [ [ 1; 2 ]; [ 3 ] ]
             || Base.List.equal (Base.List.equal Core.Int.equal) norm [ [ 3 ]; [ 1; 2 ] ]));
      pin "WTO-24" "WTO-SCC: two cycles joined by a bridge stay two components (each node exactly once)"
        (fun () ->
          let module Int_scc = Cw.Scc (struct
              type t = int
              let compare = compare
            end) in
          let jparts =
            Int_scc.partition [ 1; 2; 3; 4 ]
              (fun n ->
                if n = 1 then [ 2 ]
                else if n = 2 then [ 1; 3 ]
                else if n = 3 then [ 4 ]
                else if n = 4 then [ 3 ]
                else [])
              (fun n ->
                if n = 1 then [ 2 ]
                else if n = 2 then [ 1 ]
                else if n = 3 then [ 2; 4 ]
                else if n = 4 then [ 3 ]
                else [])
          in
          check "WTO-24"
            (let sets = Base.List.map jparts ~f:(Core.Set.of_list (module Core.Int)) in
             List.length sets = 2
             && Base.List.for_all sets ~f:(fun st -> Core.Set.length st = 2)
             && List.length (List.concat jparts) = 4
             && Base.List.exists sets ~f:(fun st -> Core.Set.mem st 1 && Core.Set.mem st 2)
             && Base.List.exists sets ~f:(fun st -> Core.Set.mem st 3 && Core.Set.mem st 4)
             && not
                  (Base.List.exists sets ~f:(fun st ->
                       Core.Set.mem st 1 && Core.Set.mem st 3))));
    ]
  @ [
      (* The dispatch-graph adapter over the plain -O0 dispatch shape. *)
      pin "WTO-25"
        "DG-SUCC: the resolved in-sub targets ride the dispatch block's successors (filtered, deduplicated)"
        (fun () ->
          let _sub, entry, b1, b2, foreign, _blocks, succs, _preds = mk_dg_dispatch () in
          check "WTO-25"
            (List.length (succs entry) = 2
             && Base.List.count (succs entry) ~f:(Tid.equal b1) = 1
             && Base.List.mem (succs entry) b2 ~equal:Tid.equal
             && not (Base.List.mem (succs entry) foreign ~equal:Tid.equal)));
      pin "WTO-26" "DG-PRED: the extra edge mirrors into the fresh target's predecessor list"
        (fun () ->
          let _sub, entry, _b1, b2, _foreign, _blocks, _succs, preds = mk_dg_dispatch () in
          check "WTO-26" (Base.List.equal Tid.equal (preds b2) [ entry ]));
      pin "WTO-27" "DG-PRED: a base successor's predecessor list keeps no duplicate mirror"
        (fun () ->
          let _sub, entry, b1, _b2, _foreign, _blocks, _succs, preds = mk_dg_dispatch () in
          check "WTO-27" (Base.List.equal Tid.equal (preds b1) [ entry ]));
      pin "WTO-28" "DG-EMPTY: an empty resolved map is the plain CFG"
        (fun () ->
          let sub, entry, b1, b2, _foreign, blocks, _succs, _preds = mk_dg_dispatch () in
          let { Dg.succs = plain_succs; Dg.preds = plain_preds; Dg.gained_preds = _ } =
            Dg.make ~cfg:(cfg_of sub) ~blocks Tid.Map.empty sub
          in
          check "WTO-28"
            (Base.List.equal Tid.equal (plain_succs entry) [ b1 ]
             && Base.List.is_empty (plain_preds b2)));
      pin "WTO-29" "DG-WTO: the extra edge alone closes the loop's WTO component"
        (fun () ->
          let nodes2, l0, l1, l2, loop_succs, loop_preds = mk_dg_loop () in
          let comps = Cw.wto ~nodes:nodes2 ~succ:loop_succs ~pred:loop_preds in
          check "WTO-29"
            (match comps with
             | Cw.SCC (h, inner) :: _ ->
               Tid.equal h l0
               && Core.Set.equal
                    (Core.Set.of_list (module Tid) (members (Cw.SCC (h, inner))))
                    (Core.Set.of_list (module Tid) [ l0; l1; l2 ])
             | _ -> false));
      pin "WTO-30" "ROWS-ENGINE: the completed dispatch's case edges are term edges (one per target)"
        (fun () ->
          let entry, b1, b2, succs, _preds = mk_rows_dispatch () in
          check "WTO-30"
            (Base.List.count (succs entry) ~f:(Tid.equal b1) = 1
             && Base.List.count (succs entry) ~f:(Tid.equal b2) = 1));
      pin "WTO-31" "ROWS-ENGINE: the case target mirrors into preds"
        (fun () ->
          let entry, _b1, b2, _succs, preds = mk_rows_dispatch () in
          check "WTO-31" (Base.List.equal Tid.equal (preds b2) [ entry ]));
    ]

let () = run "wto" tests
