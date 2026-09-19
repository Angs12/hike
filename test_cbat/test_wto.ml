(* The WTO module's ordering contracts: the comp accessors, the
   Bourdoncle properties over explicit graphs (every vertex once, heads
   on cycles, every loop's Cw.SCC is one component carrying a head), the
   nesting/sequencing shapes, and the Kosaraju partition the
   construction is built on. *)
open Bap.Std
open Core
open Test_common
open Test_fixtures

module Cw = Cbat_vsa__Cbat_wto
module Dg = Cbat_vsa__Cbat_dispatch_graph
module Sm = Hike.Stack_model
module Hv = Hike.Vsa

module Tid_scc = Cw.Scc (struct
    type t = Tid.t
    let compare = Tid.compare
  end)

(* Explicit graphs: a node list + an edge list; the accessors read the
   edge list. *)
let succs edges n = List.filter_map edges ~f:(fun (u, v) -> if Tid.equal u n then Some v else None)
let preds edges n = List.filter_map edges ~f:(fun (u, v) -> if Tid.equal v n then Some u else None)
let wto_of nodes edges = Cw.wto ~nodes ~succ:(succs edges) ~pred:(preds edges)

let rec members (c : Cw.comp) : Tid.t list =
  match c with
  | Cw.Vertex v -> [ v ]
  | Cw.SCC (h, inner) -> h :: List.concat_map inner ~f:members

(* Every Cw.SCC component of the forest with its full member set. *)
let rec scc_comps (cs : Cw.comp list) : (Tid.t * Tid.t list) list =
  List.concat_map cs ~f:(function
      | Cw.Vertex _ -> []
      | Cw.SCC (h, inner) -> (h, members (Cw.SCC (h, inner))) :: scc_comps inner)

let heads_set comps = Core.Set.of_list (module Tid) (List.map (scc_comps comps) ~f:fst)

let inner_comps (cs : Cw.comp list) : Cw.comp list =
  List.concat_map cs ~f:(function Cw.Vertex _ -> [] | Cw.SCC (_, inner) -> inner)

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

(* The Bourdoncle battery over one graph: vertex coverage, heads are
   exactly cycle-bound widening points, every loop's Cw.SCC is one WTO
   component carrying a head. *)
let check_wto_battery (label : string) (nodes : Tid.t list) (edges : (Tid.t * Tid.t) list) : unit =
  let comps = wto_of nodes edges in
  let flat = Cw.flatten_comps comps in
  check (label ^ ": every vertex appears exactly once in the flattened order")
    (List.length flat = List.length nodes
     && Core.Set.equal (Core.Set.of_list (module Tid) flat) (Core.Set.of_list (module Tid) nodes));
  let hs = heads_set comps in
  check (label ^ ": every head lies on a cycle (no spurious widening points)")
    (Core.Set.for_all hs ~f:(on_a_cycle edges));
  let gsccs =
    Tid_scc.partition nodes (succs edges) (preds edges)
    |> List.filter ~f:(fun c -> List.length c > 1 || on_a_cycle edges (List.hd_exn c))
    |> List.map ~f:(Core.Set.of_list (module Tid))
  in
  let wsccs = List.map (scc_comps comps) ~f:(fun (_, ms) -> Core.Set.of_list (module Tid) ms) in
  check (label ^ ": every nontrivial graph SCC is exactly one WTO component's member set")
    (List.for_all gsccs ~f:(fun g -> List.exists wsccs ~f:(Core.Set.equal g)));
  check (label ^ ": every nontrivial graph SCC contains one of the heads")
    (List.for_all gsccs ~f:(fun ms -> not (Core.Set.is_empty (Core.Set.inter ms hs))));
  check (label ^ ": heads_of_comps is exactly the forest's head set")
    (Core.Set.equal (Cw.heads_of_comps comps) hs)

(* The dispatch-graph adapter: a Resolved dispatch's extra edges ride
   the dispatching block's successors and mirror into the targets'
   predecessor lists; non-blocks are filtered, base successors are not
   duplicated, an empty resolved map is the plain CFG, and the WTO
   component closes on an extra edge alone. *)
let cfg_of (sub : sub term) : Graphs.Tid.t =
  Graphs.Tid.Node.remove Graphs.Tid.exit
    (Graphs.Tid.Node.remove Graphs.Tid.start (Sub.to_graph sub))

let run_dispatch_graph () =
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
  let { Dg.succs = succs; Dg.preds = preds } =
    Dg.make ~cfg:(cfg_of sub) ~blocks resolved sub
  in
  check "DG-SUCC: the resolved in-sub targets ride the dispatch block's successors (filtered, deduplicated)"
    (List.length (succs entry) = 2
     && Base.List.count (succs entry) ~f:(Tid.equal b1) = 1
     && List.mem (succs entry) b2 ~equal:Tid.equal
     && not (List.mem (succs entry) foreign ~equal:Tid.equal));
  check "DG-PRED: the extra edge mirrors into the fresh target's predecessor list"
    (List.equal Tid.equal (preds b2) [ entry ]);
  check "DG-PRED: a base successor's predecessor list keeps no duplicate mirror"
    (List.equal Tid.equal (preds b1) [ entry ]);
  let { Dg.succs = plain_succs; Dg.preds = plain_preds } =
    Dg.make ~cfg:(cfg_of sub) ~blocks Tid.Map.empty sub
  in
  check "DG-EMPTY: an empty resolved map is the plain CFG"
    (List.equal Tid.equal (plain_succs entry) [ b1 ]
     && List.is_empty (plain_preds b2));
  let sub2, tids2 =
    sub_of "dg_loop"
      [ [], [ (1, mk_goto) ];
        [], [ (2, mk_goto) ];
        [], [ (3, mk_goto) ];
        [], [ (0, mk_ret) ] ]
  in
  let l0 = tids2.(0) and l1 = tids2.(1) and l2 = tids2.(2) in
  let { Dg.succs = loop_succs; Dg.preds = loop_preds } =
    Dg.make ~cfg:(cfg_of sub2)
      ~blocks:(Core.Set.of_list (module Tid) (Array.to_list tids2))
      (Core.Map.singleton (module Tid) (Term.tid (sub_jmp sub2 2 0))
         (Core.Set.singleton (module Tid) l0))
      sub2
  in
  let comps =
    Cw.wto ~nodes:(Array.to_list tids2) ~succ:loop_succs ~pred:loop_preds
  in
  check "DG-WTO: the extra edge alone closes the loop's WTO component"
    (match comps with
     | Cw.SCC (h, inner) :: _ ->
       Tid.equal h l0
       && Core.Set.equal
            (Core.Set.of_list (module Tid) (members (Cw.SCC (h, inner))))
            (Core.Set.of_list (module Tid) [ l0; l1; l2 ])
     | _ -> false)

(* The completed dispatch's graph view: the guarded-goto series lives
   in the BIR, so the case edges ARE term edges — the dispatch graph's
   resolved argument is empty and the engine's succs/preds read the
   rewrite's one-edge-per-target series. *)
let run_rows_engine () =
  let sub, tids =
    sub_of "rows_dispatch"
      [ [],
        [ (1, fun t -> Jmp.create ~cond:(Bil.BinOp (Bil.EQ, Bil.Var (v64 "rows_sel"), Bil.Int (Cbat_word.to_word (w64 0x1010)))) (Goto (Direct t)));
          (2, mk_goto) ];
        [], [ (0, mk_ret) ];
        [], [ (0, mk_ret) ] ]
  in
  let entry = tids.(0) and b1 = tids.(1) and b2 = tids.(2) in
  let { Dg.succs; preds } =
    Dg.make ~cfg:(cfg_of sub)
      ~blocks:(Core.Set.of_list (module Tid) (Array.to_list tids))
      Tid.Map.empty sub
  in
  check "ROWS-ENGINE: the completed dispatch's case edges are term edges (one per target)"
    (Base.List.count (succs entry) ~f:(Tid.equal b1) = 1
     && Base.List.count (succs entry) ~f:(Tid.equal b2) = 1);
  check "ROWS-ENGINE: the case target mirrors into preds"
    (List.equal Tid.equal (preds b2) [ entry ])

let run () =
  (* The accessor contracts over a hand-built forest. *)
  let a = Tid.create () in
  let h = Tid.create () in
  let b = Tid.create () in
  let i = Tid.create () in
  let c = Tid.create () in
  let d = Tid.create () in
  let hand = [ Cw.Vertex a; Cw.SCC (h, [ Cw.Vertex b; Cw.SCC (i, [ Cw.Vertex c ]) ]); Cw.Vertex d ] in
  check "WTO-FLATTEN: all blocks, and heads precede their members"
    (List.equal Tid.equal (Cw.flatten_comps hand) [ a; h; b; i; c; d ]);
  check "WTO-HEADS: heads_of_comps reaches the innermost SCCs (vertices contribute none)"
    (Core.Set.equal (Cw.heads_of_comps hand) (Core.Set.of_list (module Tid) [ h; i ]));

  (* Acyclic diamond: no heads, every vertex a plain component. *)
  let n0 = Tid.create () and n1 = Tid.create () and n2 = Tid.create () and n3 = Tid.create () in
  let diamond_edges = [ (n0, n1); (n0, n2); (n1, n3); (n2, n3) ] in
  let dcomps = wto_of [ n0; n1; n2; n3 ] diamond_edges in
  check "WTO-ACYCLIC: an acyclic graph produces no heads"
    (Core.Set.is_empty (Cw.heads_of_comps dcomps));
  check "WTO-ACYCLIC: an acyclic graph's components are all vertices"
    (List.for_all dcomps ~f:(function Cw.Vertex _ -> true | Cw.SCC _ -> false));

  (* Self-loop: the single vertex is its own head. *)
  let s = Tid.create () in
  let scomps = wto_of [ s ] [ (s, s) ] in
  check "WTO-SELF: a self-looping vertex heads its own SCC"
    (match scomps with
     | [ Cw.SCC (hd, inner) ] -> Tid.equal hd s && Core.List.is_empty inner
     | _ -> false);

  (* Two-node cycle: the head precedes its member (heads-in-component). *)
  let ca = Tid.create () and cb = Tid.create () in
  let ccomps = wto_of [ ca; cb ] [ (ca, cb); (cb, ca) ] in
  check "WTO-CYCLE: one SCC headed by the cycle's entry"
    (match ccomps with
     | [ Cw.SCC (hd, inner) ] -> Tid.equal hd ca && List.equal Tid.equal (Cw.flatten_comps inner) [ cb ]
     | _ -> false);
  check "WTO-CYCLE: the flattened order puts the head first"
    (List.equal Tid.equal (Cw.flatten_comps ccomps) [ ca; cb ]);

  (* Integrated shape: entry -> outer loop {h1 with inner loop {i}} ->
     second loop {l2} -> exit. Pins the component structure and the
     traversal order: heads first, the inner loop stabilizes before the
     outer tail, sequential loops stay siblings in order. *)
  let e = Tid.create () and h1 = Tid.create () and iv = Tid.create () and j = Tid.create () in
  let k = Tid.create () and l2 = Tid.create () and b2 = Tid.create () and x = Tid.create () in
  let nodes = [ e; h1; iv; j; k; l2; b2; x ] in
  let edges =
    [ (e, h1); (h1, iv); (iv, j); (j, iv); (iv, k); (k, h1); (h1, l2); (l2, b2); (b2, l2); (l2, x) ]
  in
  let comps = wto_of nodes edges in
  check_wto_battery "WTO-GRAPH" nodes edges;
  check "WTO-GRAPH: the heads are exactly the three loop heads"
    (Core.Set.equal (Cw.heads_of_comps comps) (Core.Set.of_list (module Tid) [ h1; iv; l2 ]));
  check "WTO-GRAPH: the inner loop's SCC is nested inside the outer loop's SCC"
    (match List.find_map comps ~f:(function
             | Cw.SCC (h, inner) when Tid.equal h h1 -> Some inner
             | _ -> None) with
     | Some inner ->
       List.exists inner ~f:(fun ic ->
           match comp_head ic with Some h2 -> Tid.equal h2 iv | None -> false)
     | None -> false);
  check "WTO-GRAPH: heads first, then the inner body, then the outer tail, then the next loop"
    (List.equal Tid.equal (Cw.flatten_comps comps) [ e; h1; iv; j; k; l2; b2; x ]);
  check "WTO-GRAPH: the inner loop's members stabilize before the outer tail (inner-before-outer)"
    (let flat = Cw.flatten_comps comps in
     pos_of flat iv < pos_of flat k && pos_of flat j < pos_of flat k);
  check "WTO-GRAPH: sequential loops are sibling components in traversal order"
    (let flat = Cw.flatten_comps comps in
     match List.find_map (scc_comps comps) ~f:(fun (hd, ms) -> if Tid.equal hd h1 then Some ms else None) with
     | Some ms -> not (List.exists ms ~f:(Tid.equal l2)) && pos_of flat h1 < pos_of flat l2
     | None -> false);

  (* Swapped accessors build the reversed ordering: the same battery
     over the reversed edge list. *)
  let redges = List.map edges ~f:(fun (u, v) -> (v, u)) in
  check_wto_battery "WTO-REVERSED" nodes redges;

  (* The Kosaraju partition underneath: exact components, disjoint. *)
  let module Int_scc = Cw.Scc (struct
      type t = int
      let compare = compare
    end) in
  let iparts = Int_scc.partition [ 1; 2; 3 ]
      (fun n -> if n = 1 then [ 2 ] else if n = 2 then [ 1 ] else [])
      (fun n -> if n = 1 then [ 2 ] else if n = 2 then [ 1 ] else []) in
  check "WTO-SCC: the partition isolates the cycle and the singleton"
    (let norm = List.map iparts ~f:(fun l -> List.sort ~compare:Int.compare l) in
     List.equal (Base.List.equal Int.equal) norm [ [ 1; 2 ]; [ 3 ] ]
     || List.equal (Base.List.equal Int.equal) norm [ [ 3 ]; [ 1; 2 ] ]);
  let jparts = Int_scc.partition [ 1; 2; 3; 4 ]
      (fun n -> if n = 1 then [ 2 ] else if n = 2 then [ 1; 3 ] else if n = 3 then [ 4 ] else if n = 4 then [ 3 ] else [])
      (fun n -> if n = 1 then [ 2 ] else if n = 2 then [ 1 ] else if n = 3 then [ 2; 4 ] else if n = 4 then [ 3 ] else []) in
  check "WTO-SCC: two cycles joined by a bridge stay two components (each node exactly once)"
    (let sets = List.map jparts ~f:(Core.Set.of_list (module Int)) in
     List.length sets = 2
     && List.for_all sets ~f:(fun st -> Core.Set.length st = 2)
     && List.length (List.concat jparts) = 4
     && List.exists sets ~f:(fun st -> Core.Set.mem st 1 && Core.Set.mem st 2)
     && List.exists sets ~f:(fun st -> Core.Set.mem st 3 && Core.Set.mem st 4)
     && not (List.exists sets ~f:(fun st -> Core.Set.mem st 1 && Core.Set.mem st 3)));
  run_dispatch_graph ();
  run_rows_engine ()
