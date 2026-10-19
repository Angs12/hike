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

include Core
open Bap.Std
open Bap_core_theory
open Graphlib.Std

module Stages = Cbat_vsa_stages

module AI = Cbat_ai_representation
module Call_effects = Cbat_call_effects
module WordSet = Cbat_clp_set_composite
module Mem = Cbat_ai_memmap
module Word_ops = Cbat_word
module Utils = Cbat_vsa_utils

(* Re-exported so the hike library can count KB operations too. *)
#ifdef VSA_DEBUG
module Cbat_kb_census = Cbat_kb_census
module Cbat_attr_census = Cbat_attr_census
#endif

(* A head widens only after this many warmup visits. *)
let head_warmup_visits = 10

(* The fixpoint's visit budget grows with the sub: every block is
   allowed [visits_per_level] visits per loop level it sits in (its WTO
   depth, a head counting its own loop) — a level covers a head's warmup
   and the widening and landmark rounds after it — and the floor keeps a
   small sub's allowance. *)
let min_visit_budget = 6000
let visits_per_level = 64

let visit_budget (wto : Cbat_wto.comp list) : int =
  let rec go depth acc (c : Cbat_wto.comp) =
    match c with
    | Cbat_wto.Vertex _ -> acc + (visits_per_level * (depth + 1))
    | Cbat_wto.SCC (_, cs) ->
      List.fold cs ~init:(acc + (visits_per_level * (depth + 2))) ~f:(go (depth + 1))
  in
  Stdlib.max min_visit_budget (List.fold wto ~init:0 ~f:(go 0))

(* WTO over the engine cfg; [succ]/[pred] are the dispatch graph's
   accessors — the resolved dispatches' extra edges ride BOTH, so the
   ordering closes on the same graph pair it walks. *)
let wto_of_cfg ~(succ : tid -> tid list) ~(pred : tid -> tid list)
    (cfg : Graphs.Tid.t) : Cbat_wto.comp list =
  Cbat_wto.wto
    ~nodes:(Graphs.Tid.nodes cfg |> Seq.to_list)
    ~succ ~pred


(* Solution still changing at the step cap. *)
exception Fixpoint_not_converged of int * (tid, AI.t) Solution.t

type vsa_sol = (tid, AI.t) Solution.t



(* The sub's entry block: the first block in term order among the block
   graph's roots (the start node's successors).  A term can carry several
   roots — a re-lifted main holds each flattened callee's entry — and the
   entry is the block the sub's own execution starts at, which the lift
   put first in the term. *)
let entry_block_of (sub : sub term) : blk term option =
  let cfg = Sub.to_graph sub in
  let roots =
    Graphs.Tid.Node.succs Graphs.Tid.start cfg
    |> Seq.filter ~f:(fun tid -> not (Tid.equal tid Graphs.Tid.exit))
    |> Seq.to_list
    |> Core.Set.of_list (module Tid)
  in
  if Core.Set.is_empty roots then None
  else
    Term.enum blk_t sub |> Seq.find ~f:(fun b -> Core.Set.mem roots (Term.tid b))

let init_sol ~(abi : Hike_abi.t) ?entry (sub : sub term) =
  let empty_map = Tid.Map.empty in
  let msb = entry_block_of sub in
  let entry_state = Option.value ~default:AI.top entry in
  (* The default entry seeds the SP with the SYMBOLIC SEGMENT BASE:
     every SP-derived address denotes [StackOff]; explicit fixture
     entries keep their own words. *)
  let entry_state =
    match entry with
    | None ->
      AI.add_word entry_state
        ~key:(Var.base abi.Hike_abi.sp)
        ~data:(WordSet.stack_word_i64 0L)
      |> fun e -> AI.add_word e ~key:(Var.base abi.Hike_abi.thread_pointer)
          ~data:(WordSet.set_origin Hike_origin.Fs (WordSet.stack_word_i64 0L))
    | Some e -> e in
  let set_init sb = Map.set empty_map ~key:(Term.tid sb) ~data:entry_state in
  let base_map = Option.value_map ~default:empty_map ~f:set_init msb in
  (* A partial CFG is unsound; out-of-graph blocks read bottom. *)
  Solution.create base_map AI.bottom

(* Per-sub def-chain map over the sub's defs in order. *)
let defs_of (defs : def term list) : (def term * bool) Var.Map.t =
  List.fold defs ~init:Var.Map.empty ~f:begin fun m d ->
    let key = Def.lhs d in
    match Core.Map.find m key with
    | None -> Core.Map.set m ~key ~data:(d, true)
    | Some _ -> Core.Map.set m ~key ~data:(d, false)
  end

(* The run's context: the library builder plus production's own defaults —
   the non-negativity oracle over the sub's defs and stores, and the run's
   sub-address lookup.  The fixpoint and the fixtures' seam build the same
   context through this one builder. *)
let mk_rctx_with_oracle ~(abi : Hike_abi.t) ~def_reads ~def_writes
    ~phi_writes ~jmp_reads ~(synth : Hike_synth.table ref) ?sub_lookup
    (s : sub term) :
    Cbat_runctx.refine_ctx =
  let rctx =
    Cbat_runctx.mk_rctx ~abi ~def_reads ~def_writes ~phi_writes
      ~jmp_reads ~synth ?sub_lookup s
  in
  let all_defs =
    Term.enum blk_t s |> Seq.concat_map ~f:(Term.enum def_t) |> Seq.to_list in
  let defs = defs_of all_defs in
  (* The stores grouped by their address exp: the witness reads the
     matching group, never every store in the sub. *)
  let store_index =
    Base.List.fold all_defs ~init:Exp.Map.empty ~f:(fun acc d ->
        match Def.rhs d with
        | Bil.Store (_, addr', _, _, _) ->
          Core.Map.add_multi acc ~key:addr' ~data:d
        | _ -> acc)
  in
  { rctx with
    Cbat_runctx.rc_nonneg =
      (fun ~env e -> Cbat_backward.prove_nonneg ~defs ~index:store_index ~env e) }

(* Preserved registers: the convention's SP plus its callee-saved GPRs. *)
let preserved_of_sub ~(abi : Hike_abi.t) ~(synth : Hike_synth.table)
    ~def_reads (s : sub term) :
    Int.Set.t =
  let regs =
    abi.Hike_abi.sp :: abi.Hike_abi.thread_pointer :: abi.Hike_abi.callee_saved
    |> Var.Set.of_list in
  let virt =
    Term.enum blk_t s
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.fold ~init:Var.Set.empty ~f:begin fun acc d ->
      let acc =
        if Hike_synth.is_temporary ~table:synth (Def.lhs d)
        then Core.Set.add acc (Var.base (Def.lhs d)) else acc in
      def_reads d
      |> Core.Set.fold ~init:acc ~f:begin fun acc v ->
        if Hike_synth.is_temporary ~table:synth v
        then Core.Set.add acc (Var.base v) else acc
      end
    end in
  Cbat_var_id.intern_set (Core.Set.union regs virt)


(* Per-sub static edge table: per (block, jmp) accumulated cond, in
   the completed (negation-free) form. *)
let edge_conds_of (sub : sub term) : exp Tid.Map.t Tid.Map.t =
  let ircfg = Sub.to_cfg sub in
  Graphs.Ir.edges ircfg
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc e ->
      let src = Term.tid (Graphs.Ir.Node.label (Graphs.Ir.Edge.src e)) in
      let jmp = Term.tid (Graphs.Ir.Edge.jmp e) in
      let cond = Cbat_vsa_utils.complete_cond (Graphs.Ir.Edge.cond e ircfg) in
      Core.Map.update acc src ~f:(fun by_jmp ->
          Core.Map.set (Option.value by_jmp ~default:Tid.Map.empty)
            ~key:jmp ~data:cond))

(* Per-sub disabled-continuation table: each jmp observes the NEXT
   jmp's cond — the excluded edge whose exclusion becomes a landmark. *)
let disabled_conds_of ~(edge_conds : exp Tid.Map.t Tid.Map.t)
    (sub : sub term) : exp Tid.Map.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc b ->
      let js = Term.enum jmp_t b |> Seq.to_list in
      let cond j =
        Option.bind (Core.Map.find edge_conds (Term.tid b)) ~f:(fun by_jmp ->
            Core.Map.find by_jmp (Term.tid j)) in
      let rec pair js dcs acc =
        match js, dcs with
        | [], _ | _, [] -> acc
        | j :: js, Some e :: dcs ->
          pair js dcs (Core.Map.set acc ~key:(Term.tid j) ~data:e)
        | _ :: js, None :: dcs -> pair js dcs acc in
      match List.map js ~f:cond with
      | [] -> acc
      | _ :: tl -> pair js tl acc)

(* The widen cycle's need set: the block SCC's variable SCCs (a
   singleton variable SCC needs itself iff self-looping; every
   multi-vertex variable SCC needs all its members).  A phi reads its
   operands; a cycle of phis alone only carries values defined outside
   it, so it needs nothing. *)
let compute_need ~def_reads ~phi_reads
    ~(rc_blocks : Cbat_runctx.block_facts Tid.Map.t)
    (blocks : Tid.Set.t) : Var.Set.t =
  let terms =
    Core.Set.to_list blocks
    |> List.concat_map ~f:(fun tid ->
        match Core.Map.find rc_blocks tid with
        | Some bf ->
          List.map (Term.enum phi_t bf.bf_term |> Seq.to_list)
            ~f:(fun p -> (Phi.lhs p, phi_reads p, true))
          @ List.map (Term.enum def_t bf.bf_term |> Seq.to_list)
              ~f:(fun d -> (Def.lhs d, def_reads d, false))
        | None -> [])
  in
  let cycle_vars = Var.Set.of_list (List.map terms ~f:(fun (l, _, _) -> l)) in
  let phi_only =
    List.fold terms ~init:cycle_vars ~f:(fun acc (l, _, is_phi) ->
        if is_phi then acc else Core.Set.remove acc l) in
  if Core.Set.is_empty cycle_vars then Var.Set.empty
  else begin
    let succ_tbl : (Var.t, Var.t list) Hashtbl.t = Hashtbl.create (module Var) in
    let pred_tbl : (Var.t, Var.t list) Hashtbl.t = Hashtbl.create (module Var) in
    List.iter terms ~f:(fun (lhs, reads, _) ->
      Core.Set.iter reads ~f:(fun u ->
        if Core.Set.mem cycle_vars u then begin
          Hashtbl.add_multi succ_tbl ~key:lhs ~data:u;
          Hashtbl.add_multi pred_tbl ~key:u ~data:lhs
        end));
    let module Var_scc = Cbat_wto.Scc (Var) in
    let comps =
      Var_scc.partition (Core.Set.to_list cycle_vars)
        (Hashtbl.find_multi succ_tbl) (Hashtbl.find_multi pred_tbl) in
    let needs vs = not (List.for_all vs ~f:(Core.Set.mem phi_only)) in
    List.fold comps ~init:Var.Set.empty ~f:(fun need comp ->
        match comp with
        | [v] ->
          let succs = Hashtbl.find_multi succ_tbl v in
          if List.mem succs v ~equal:Var.equal && needs comp then
            Core.Set.add need v
          else need
        | _ :: _ :: _ as vs when needs vs ->
          List.fold vs ~init:need ~f:(fun need v ->
              Core.Set.add need v)
        | _ -> need)
  end

(* The round-down idiom [(x >> k) << k] with a literal k is the mask
   [x & ~(2^k - 1)]; the mask form computes exactly on a stack-symbolic
   operand, while the shifts alone read the base's unknown bits and
   answer top.  The idiom spans two defs ([v1 := x >> k] ... later ...
   [v2 := v1 << k]), with flag defs reading the shifted value between:
   the rewrite inserts a temp [t := x] BEFORE the shift def and rewrites
   ONLY the shift-back to [t & ~(2^k - 1)] — the shift def and every
   reader of it keep the true value, and the shift-back is the mask
   identity exactly. *)
type rewrite = [ `Mask of var * exp * word | `Temp of var * exp * word ]

let normalize_round_with_synth ~(synth : Hike_synth.table ref)
    (s : Sub.t) : Sub.t =
  let mask_of (k : word) (w : int) : word option =
    let kk = Word.to_int64_exn k in
    if w > 0 && w <= 64 && Stdlib.Int64.compare kk 0L > 0
       && Stdlib.Int64.compare kk (Int64.of_int w) < 0
    then
      Some
        (Word.of_int64 ~width:w
           (Stdlib.Int64.neg (Stdlib.Int64.shift_left 1L (Option.value_exn (Int64.to_int kk)))))
    else None
  in
  let width_of (x : exp) : int =
    match x with
    | Bil.Var v -> (match Var.typ v with Type.Imm n -> n | _ -> 64)
    | _ -> 64
  in
  let rewrites =
    Term.enum blk_t s
    |> Seq.fold
         ~init:(Tid.Map.empty : rewrite Tid.Map.t)
         ~f:(fun acc blk ->
        (* The shift defs seen so far, by lhs. *)
        (* Each lhs whose LAST def is the shift; a redefinition
           retires the entry (the shift-back would read the new
           value). *)
        let shifted : (def term * exp * word * int) Var.Map.t ref =
          ref Var.Map.empty
        in
        let retire v = shifted := Core.Map.remove !shifted v in
        Term.enum def_t blk
        |> Seq.fold ~init:acc ~f:(fun acc d ->
            let acc =
              match Def.rhs d with
              | Bil.BinOp (Bil.LSHIFT, Bil.Var v, Bil.Int j) -> (
                  match Core.Map.find !shifted v with
                  | Some (d0, x, k, w) when Word.equal k j -> (
                      match mask_of k w with
                      | Some mask ->
                          let synth', t =
                            Hike_synth.mint_fresh ~bits:w Hike_synth.Refinement
                              !synth in
                          synth := synth';
                          (* d0's tid keys the temp insertion; d's tid keys
                             the mask rewrite. *)
                          let m =
                            Core.Map.set acc ~key:(Term.tid d)
                              ~data:(`Mask (t, x, mask))
                          in
                          Core.Map.set m ~key:(Term.tid d0)
                            ~data:(`Temp (t, x, mask))
                      | None -> acc)
                  | _ -> acc)
              | _ -> acc
            in
            retire (Def.lhs d);
            (match Def.rhs d with
             | Bil.BinOp (Bil.RSHIFT, x, Bil.Int k) ->
               shifted := Core.Map.set !shifted ~key:(Def.lhs d)
                 ~data:(d, x, k, width_of x)
             | _ -> ());
            acc))
  in
  if Core.Map.is_empty rewrites then s
  else
    Term.map blk_t s ~f:(fun blk ->
        let has_rewrite =
          Term.enum def_t blk
          |> Seq.exists ~f:(fun d -> Core.Map.mem rewrites (Term.tid d))
        in
        if not has_rewrite then blk
        else
          Term.concat_map def_t blk ~f:(fun d ->
              match Core.Map.find rewrites (Term.tid d) with
              | Some (`Mask (t, _, mask)) ->
                [ Def.with_rhs d (Bil.BinOp (Bil.AND, Bil.Var t, Bil.Int mask)) ]
              | Some (`Temp (t, x, _)) ->
                (* The temp reads [x] before the shift overwrites it. *)
                [ Def.create t x; d ]
              | None -> [ d ]))

let normalize_round (s : Sub.t) : Sub.t =
  normalize_round_with_synth ~synth:(ref Hike_synth.empty) s

#ifdef VSA_DEBUG
(* Forward witness: every guard cond from [p] to [v] denotates false on
   the pred's entry state, so the edge is dead without the backward
   refinement.  A dispatch extra-edge has no jmp and cannot be
   witnessed. *)
let edge_forward_dead ~(rctx : Cbat_runctx.refine_ctx) ~edge_conds ~get
    ~(p : Tid.t) ~(v : Tid.t) : bool =
  match Core.Map.find rctx.rc_blocks p with
  | None -> false
  | Some bf ->
    let conds = Core.Map.find edge_conds p in
    Term.enum jmp_t bf.bf_term
    |> Seq.filter ~f:(fun j ->
        match Jmp.kind j with
        | Goto (Direct t) | Ret (Direct t) -> Tid.equal t v
        | Call c -> (
            match Call.return c with
            | Some (Direct t) -> Tid.equal t v
            | _ -> false)
        | Goto (Indirect _) | Ret (Indirect _) | Int _ -> false)
    |> Seq.exists ~f:(fun j ->
        match
          Option.bind conds ~f:(fun m -> Core.Map.find m (Term.tid j))
        with
        | None -> false
        | Some cond -> (
            match Cbat_transfer.denote_imm_exp ~synth:!(rctx.rc_synth) cond (get p) with
            | Ok w -> not (WordSet.elem Cbat_word.b1 w)
            | Error _ -> false))

(* The dead-edge census of one denoted edge. *)
let debug_edge_result ~rctx ~edge_conds ~get ~p ~v (res : AI.t) : unit =
  Cbat_attr_census.bump "bottomskip.edge.total";
  if AI.equal res AI.bottom then begin
    Cbat_attr_census.bump "bottomskip.edge.bottom";
    if edge_forward_dead ~rctx ~edge_conds ~get ~p ~v then
      Cbat_attr_census.bump "bottomskip.edge.forward_dead"
    else Cbat_attr_census.bump "bottomskip.edge.refine_only"
  end

(* The dead-edge census of one block entry. *)
let debug_entry ~rctx ~edge_conds ~get ~preds ~v (incoming : AI.t) : unit =
  if not (List.is_empty preds) then begin
    Cbat_attr_census.bump "bottomskip.entry.total";
    if AI.equal incoming AI.bottom then begin
      Cbat_attr_census.bump "bottomskip.entry.bottom";
      if List.for_all preds ~f:(fun p ->
          edge_forward_dead ~rctx ~edge_conds ~get ~p ~v)
      then Cbat_attr_census.bump "bottomskip.entry.forward_dead"
      else Cbat_attr_census.bump "bottomskip.entry.refine_only"
    end
  end

(* Counts the head's arm and names it for the churn witness. *)
let debug_head_arm (arm : Cbat_landmarks.arm) : string =
  Cbat_attr_census.bump
    (match arm with
     | Cbat_landmarks.Finite _ -> "widen.head.finite"
     | Cbat_landmarks.Zero -> "widen.head.zero"
     | Cbat_landmarks.Inf -> "widen.head.inf");
  match arm with
  | Cbat_landmarks.Finite n -> Printf.sprintf "finite:%d" n
  | Cbat_landmarks.Zero -> "zero"
  | Cbat_landmarks.Inf -> "inf"

(* The churn census of one changed block state. *)
let debug_churn ~(head : bool) ~(has_widened : bool) ~(head_arm : string)
    (v : Tid.t) (old : AI.t) (new_val : AI.t) : unit =
  let mono = Stages.time `Equal (fun () -> AI.precedes old new_val) in
  Cbat_attr_census.bump
    (Printf.sprintf "churn.%s.%s" (if head then "head" else "plain")
       (if mono then "grow" else "nonmono"));
  let detail, same_repr = AI.diff old new_val in
  if same_repr > 0 then Cbat_attr_census.bump "churn.repr.same";
  if has_widened then
    Cbat_attr_census.note
      (Printf.sprintf "churn.head.%s" (Tid.name v))
      ~limit:16
      (Printf.sprintf "churn(head) %s %s arm=%s %s\n    %s"
         (Tid.name v) (if mono then "grow" else "nonmono")
         (if String.is_empty head_arm then "pre-warm" else head_arm)
         (AI.head_summary new_val) detail)
  else
    Cbat_attr_census.note
      (Printf.sprintf "churn.%s" (if head then "head" else "plain"))
      ~limit:3
      (Printf.sprintf "churn%s %s %s\n    %s"
         (if head then "(head)" else "") (Tid.name v)
         (if mono then "grow" else "nonmono") detail)
#endif

let static_graph_vsa
    ~(abi : Hike_abi.t)
    ~def_reads ~def_writes ~phi_reads ~phi_writes ~jmp_reads
    ?(callee : Tid.t -> Cbat_call_effects.callee =
        fun _ -> Cbat_call_effects.Summary None)
    ?(resolved : Tid.Set.t Tid.Map.t = Tid.Map.empty)
    ?(sub_lookup : int64 -> Tid.t option = fun _ -> None)
    ?(wake : Tid.Set.t = Tid.Set.empty)
    ~(synth : Hike_synth.table ref)
    (s : Sub.t) (init : vsa_sol) : vsa_sol =
  let s = normalize_round_with_synth ~synth s in
  let preserved = preserved_of_sub ~abi ~synth:!synth ~def_reads s in
  let edge_conds = edge_conds_of s in
  let disabled_conds = disabled_conds_of ~edge_conds s in
  (* Pseudo-nodes never reach denotation. *)
  let cfg =
    Sub.to_graph s
    |> Graphs.Tid.Node.remove Graphs.Tid.start
    |> Graphs.Tid.Node.remove Graphs.Tid.exit in
  let rctx =
    mk_rctx_with_oracle ~abi ~def_reads ~def_writes ~phi_writes
      ~jmp_reads ~synth ~sub_lookup s
  in
  (* The dispatch graph: the CFG plus the Resolved dispatches' extra
     edges, serving the WTO, the worklist, and the predecessor lists. *)
  let dg = Cbat_dispatch_graph.make ~cfg
      ~blocks:(Tid.Set.of_list (Core.Map.keys rctx.Cbat_runctx.rc_blocks))
      resolved s
  in
  let { Cbat_dispatch_graph.succs; Cbat_dispatch_graph.preds } = dg in
  let plan_of =
    Cbat_forward.plans_of ~resolved ~edge_conds ~disabled:disabled_conds ~rctx in
  (* WTO fixpoint; inner SCCs stabilize first. *)
  let wto = wto_of_cfg ~succ:succs ~pred:preds cfg in
  let smry = Cbat_wto.summary wto in
  let heads = smry.Cbat_wto.heads in
  let head_to_blocks = smry.Cbat_wto.head_to_blocks in
  let block_to_head = smry.Cbat_wto.block_to_head in
  let need_map : Core.Int.Set.t Tid.Map.t =
    Hashtbl.fold head_to_blocks ~init:Tid.Map.empty
      ~f:(fun ~key:h ~data:blocks acc ->
        Core.Map.set acc ~key:h ~data:(Cbat_var_id.intern_set (compute_need ~def_reads ~phi_reads ~rc_blocks:rctx.rc_blocks blocks)))
  in
  let scalar_store =
    let word v = match Var.typ v with Type.Imm _ -> true | _ -> false in
    if not rctx.rc_ssa then None else
    let variables = Term.enum blk_t s
      |> Seq.fold ~init:Var.Set.empty ~f:(fun vars b ->
          Blk.elts b |> Seq.fold ~init:vars ~f:(fun vars term ->
              Set.union vars (Set.union (Hike_stack_model.reads term)
                                (Hike_stack_model.writes term))))
      |> Set.filter ~f:word |> Set.to_list in
    let blocks = Map.to_alist rctx.rc_blocks |> List.map ~f:(fun (tid, bf) ->
        let locals = Term.enum def_t bf.bf_term |> Seq.map ~f:Def.lhs
          |> Seq.filter ~f:word |> Seq.to_list |> Var.Set.of_list in
        (tid, locals)) in
    let seed = Solution.enum init |> Seq.find_map ~f:(fun (_, env) ->
        if AI.equal env AI.bottom then None else Some env)
      |> Option.value ~default:AI.top in
    Some (AI.create_scalars ~variables ~blocks ~seed)
  in
  let save n env = Option.value_map scalar_store ~default:env ~f:(fun store ->
      let env = AI.enter_block store n env in
      if not (AI.equal env AI.bottom) then
        Option.iter (Map.find rctx.rc_blocks n) ~f:(fun bf ->
            ignore (Cbat_transfer.denote_defs ~synth:!synth bf.Cbat_runctx.bf_term env));
      env) in
  let sol_default = Solution.default init in
  (* The initial solution seeds the store; from here the store is the only
     home for per-block values. *)
  let sol_store =
    ref (Solution.enum init
         |> Seq.fold ~init:Tid.Map.empty
              ~f:(fun m (k, v) -> Core.Map.set m ~key:k ~data:(save k v))) in
  let get n = Option.value (Core.Map.find !sol_store n) ~default:sol_default in
  let set n v = sol_store := Core.Map.set !sol_store ~key:n ~data:(save n v) in
  let mk_sol () = Solution.create !sol_store sol_default in
  Stages.reset ();
  let total_processed = ref 0 in
  let max_steps = visit_budget wto in
  (* Per-head visit counts; each head gets its own warmup window. *)
  let head_visits : (Tid.t, int) Hashtbl.t = Hashtbl.create (module Tid) in
  let head_warmed (v : Tid.t) : bool =
    Option.value ~default:0 (Hashtbl.find head_visits v)
    > head_warmup_visits in
  (* The join of the predecessors' denoted edges: the first edge seeds
     it, each later edge joins in as it is denoted, in predecessor
     order.  Dead bindings never reach the join; the keep-set depends
     only on the visited block, not on the predecessor. *)
#ifdef VSA_DEBUG
  let head_arm = ref "" in
#endif
  let incoming_of (v : Tid.t) ~(preds : Tid.t list) ~(old : AI.t) : AI.t =
    let bf = Core.Map.find rctx.rc_blocks v in
    let keep =
      Option.value_map bf ~default:Int.Set.empty ~f:(fun bf -> bf.bf_live_ids)
    in
    (* Deliver refined operands to the destination's phi names. *)
    let bind_phis p res =
      match bf with
      | Some bf -> Cbat_transfer.denote_phis ~synth:!synth ~source:p bf.bf_term res
      | None -> res
    in
    let out p =
      Cbat_landmarks.with_widening_head rctx.Cbat_runctx.rc_landmarks
        (Hashtbl.find block_to_head p) (fun () ->
          let p_entry = Stages.time `Glue (fun () -> get p) in
          let res = Stages.time `Denote (fun () ->
              Cbat_forward.denote_block ~preserved ~callee ~plan_of
                ~rctx
                ~source:p p_entry ~target:v) in
          let res = Stages.time `Denote (fun () -> bind_phis p res) in
          let res = Stages.time `Glue (fun () ->
              match scalar_store with
              | Some _ -> AI.project ~keep ~block:v res
              | None -> res) in
#ifdef VSA_DEBUG
          debug_edge_result ~rctx ~edge_conds ~get ~p ~v res;
#endif
          res) in
    if List.is_empty preds then old
    else
      Option.value ~default:old
        (List.fold preds ~init:None ~f:(fun acc p ->
             let res = out p in
             match acc with
             | None -> Some res
             | Some a -> Some (Stages.time `Join (fun () -> AI.join a res))))
  in
  (* A warm head whose join grew widens by the landmark module's arm:
     Finite extrapolates; Zero advances and joins; Inf widens.
     Consumption is per key — each key reads its own row first, the
     head's arm is the fallback, and the clear spends only what was
     consumed. *)
  let widen_at_head (v : Tid.t) ~(old : AI.t) ~(incoming : AI.t) : AI.t =
    let need = Option.value ~default:Core.Int.Set.empty (Core.Map.find need_map v) in
    Cbat_landmarks.with_widening_head rctx.Cbat_runctx.rc_landmarks (Some v)
      (fun () ->
        let arm =
          Cbat_landmarks.head_arm rctx.Cbat_runctx.rc_landmarks v in
#ifdef VSA_DEBUG
        head_arm := debug_head_arm arm;
#endif
        match arm with
        | Cbat_landmarks.Finite n ->
          Stages.time `Widen (fun () -> AI.selective_widen_extrapolate ~head:v ~landmarks:rctx.Cbat_runctx.rc_landmarks ~need ~steps:n old incoming)
        | Cbat_landmarks.Zero ->
          Stages.time `Widen (fun () ->
              AI.advance_join_landmarks ~head:v
                ~landmarks:rctx.Cbat_runctx.rc_landmarks ~need old
                incoming)
        | Cbat_landmarks.Inf ->
          Stages.time `Widen (fun () ->
              AI.widen_with_landmarks ~head:v
                ~landmarks:rctx.Cbat_runctx.rc_landmarks ~need old
                incoming))
  in
  let process_vertex (v : Tid.t) : bool =
    Stages.time `Scaffold (fun () ->
    incr total_processed;
    (* This visit counts toward the head's own window, including itself. *)
    if Core.Set.mem heads v then begin
      let n = Option.value ~default:0 (Hashtbl.find head_visits v) in
      Hashtbl.set head_visits ~key:v ~data:(n + 1)
    end;
    if !total_processed > max_steps then begin
      let sol = mk_sol () in
      raise (Fixpoint_not_converged (max_steps, sol))
    end;
    let preds = preds v in
    let old = get v in
    (* An entry has no predecessor: its seeded boundary inputs are not
       edge-delivered phis and must not be projected away. *)
    let old =
      if List.is_empty preds then old
      else match scalar_store, Map.find rctx.rc_blocks v with
        | Some _, Some bf -> AI.project ~keep:bf.Cbat_runctx.bf_live_ids ~block:v old
        | _ -> old
    in
    let incoming = incoming_of v ~preds ~old in
#ifdef VSA_DEBUG
    debug_entry ~rctx ~edge_conds ~get ~preds ~v incoming;
    head_arm := "";
#endif
    let has_widened = Core.Set.mem heads v && head_warmed v in
    let new_val =
      if List.is_empty preds then old
      else if has_widened then begin
        let j = Stages.time `Join (fun () -> AI.join old incoming) in
        if Stages.time `Equal (fun () -> AI.equal old j)
        then old
        else widen_at_head v ~old ~incoming
      end else
        Stages.time `Join (fun () -> AI.join old incoming)
    in
    (* Bump-only-on-change: physical sharing first, then the timed compare. *)
    if phys_equal old new_val
       || Stages.time `Equal (fun () -> AI.equal old new_val)
    then false
    else begin
#ifdef VSA_DEBUG
      debug_churn ~head:(Core.Set.mem heads v) ~has_widened
        ~head_arm:!head_arm v old new_val;
#endif
      Stages.time `Glue (fun () -> set v new_val);
      true
    end)
  in
  (* Succ-seeded WTO-priority worklist; every visit runs process_vertex
     completely, and changes enqueue Tid-CFG successors.  The queue pops
     the lowest WTO position, whose block is unique: [pending] holds one
     block per position, and [unplaced] the blocks outside the WTO,
     which pop last in Tid order. *)
  let pending : Tid.t Int.Map.t ref = ref Int.Map.empty in
  let unplaced : Tid.Set.t ref = ref Tid.Set.empty in
  let enqueue t =
    match Core.Map.find smry.Cbat_wto.pos_of t with
    | Some p -> pending := Core.Map.set !pending ~key:p ~data:t
    | None -> unplaced := Core.Set.add !unplaced t
  in
  (* Entry itself is never seeded: init_sol pre-seeds its state. *)
  Option.iter (entry_block_of s) ~f:(fun entry ->
    succs (Term.tid entry)
    |> List.iter ~f:enqueue);
  (* A block that gained an extra-edge predecessor re-joins even from
     a stable warm seed — its incoming set grew without any
     predecessor's value changing. *)
  Core.Set.iter dg.Cbat_dispatch_graph.gained_preds ~f:enqueue;
  (* A woken block's successors re-join from the warm seed: its outgoing
     edges changed without any state of the walk changing (a resumed
     solve's blocked calls now have a callee summary). *)
  Core.Set.iter wake ~f:(fun b -> succs b |> List.iter ~f:enqueue);
  let pop_min () =
    match Core.Map.min_elt !pending with
    | Some (p, v) ->
      pending := Core.Map.remove !pending p;
      Some v
    | None ->
      (match Core.Set.min_elt !unplaced with
       | None -> None
       | Some v ->
         unplaced := Core.Set.remove !unplaced v;
         Some v) in
  let rec stabilize_worklist () =
    match pop_min () with
    | None -> ()
    | Some v ->
      if process_vertex v then
        succs v |> List.iter ~f:enqueue;
      stabilize_worklist () in
  stabilize_worklist ();
  Stages.report (Sub.name s);
  mk_sol ()
(* Re-exports for the mli's fixture seam. *)
type refine_ctx = Cbat_runctx.refine_ctx

(* Re-exports of the sibling transfer/forward/backward modules. *)
let set_addr_bits = Cbat_transfer.set_addr_bits

type section_image = Cbat_transfer.section_image = {
  img_lo : int64;
  img_hi : int64;
  img_bytes : Bytes.t;
  img_slots : Int64.Set.t;
}

let set_section_images = Cbat_transfer.set_section_images
let with_images = Cbat_transfer.with_images
let normalize_round_with_synth = normalize_round_with_synth
let denote_def = Cbat_transfer.denote_def
let denote_defs = Cbat_transfer.denote_defs
let denote_imm_exp = Cbat_transfer.denote_imm_exp
let reachable_jumps = Cbat_transfer.reachable_jumps
let fold_block_states = Cbat_transfer.fold_block_states
let last_defs = Cbat_transfer.last_defs

(* The Env Tag seam (the KB domain/slot, the stamp, the raw replay,
   the VSA_DEBUG differential, [denote_exp_at], and the env stamp)
   lives in Cbat_env_tag; re-exported so the consumers keep their
   [Vsa.*] paths. *)
module Env_tag = Cbat_env_tag
module Def_origin = Cbat_def_origin
let denote_exp_at = Cbat_env_tag.denote_exp_at
let stamp_envs_of_sol = Cbat_env_tag.stamp_envs_of_sol
let env_tag = Cbat_env_tag.env_tag
let set_env_tag = Cbat_env_tag.set_env_tag
let solve_denote = Cbat_env_tag.solve_denote

(* The seam's seed shape: the cond's constrained vars.  A seed's
   constraint is the state's own value for the var, so the walk reads
   each constraint from the env it walks. *)
let refine_edge ~sol ~rctx ~seeds env blk =
  (* The walked block's IN state is its entry in [sol]. *)
  Cbat_backward.refine_edge
    ~entry:(Solution.get sol (Term.tid blk))
    ~rctx ~seeds env blk

(* The walk's write census: the walked env with the per-site count of
   ACTUAL env writes — a delivery equal to the state's value writes
   nothing, so it never counts. *)
let refine_edge_count_writes ~sol ~rctx ~seeds env blk =
  let output_writes = ref 0 in
  let input_writes = ref 0 in
  let out =
    Cbat_backward.refine_edge
      ~entry:(Solution.get sol (Term.tid blk))
      ~rctx ~seeds
      ~on_write:(fun site ->
          match site with
          | Cbat_backward.Output_write -> incr output_writes
          | Cbat_backward.Input_write -> incr input_writes)
      env blk
  in
  (out, !output_writes, !input_writes)

(* The fixtures' construction seam (cbat_vsa.mli's Test_seam). *)
module Test_seam = struct

  let mem_addr_of = Cbat_def_origin.mem_addr_of
  type refine_ctx = Cbat_runctx.refine_ctx
  let denote_def ~synth d env =
    Cbat_transfer.denote_def ~synth d env
  let denote_defs ~synth blk =
    Cbat_transfer.denote_defs ~synth blk
  let denote_imm_exp ~synth e env =
    Cbat_transfer.denote_imm_exp ~synth e env
  let fold_block_states ~synth =
    Cbat_transfer.fold_block_states ~synth
  let reachable_jumps ~synth env jmps =
    Cbat_transfer.reachable_jumps ~synth env jmps
  let constrain_edge ~synth ~env ~landmarks cond =
    Cbat_backward.constrain_edge ~synth ~env ~landmarks cond
  let refine_edge_inline ~sol ~rctx ~discarded blk env cond =
    Cbat_backward.refine_edge_inline
      ~entry:(Solution.get sol (Term.tid blk)) ~rctx ~discarded blk env cond
  type cells = Cbat_backward.cell_env
  let no_cells = Cbat_backward.no_cells
  let owe_cell ce ~mem ~range ~bits ~endian pc =
    Cbat_backward.cell_add ce
      { Cbat_backward.pm = mem; prange = range; pc; pbits = bits;
        pendian = endian }
  let cells_owed ce = not (Core.Map.is_empty ce)
  let constrain_operands ~synth ~env ?cells ?nonneg ~landmarks e produced =
    Cbat_backward.constrain_operands ~synth ~env ?cells ?nonneg ~landmarks e produced
  let mk_rctx = mk_rctx_with_oracle
  let normalize_round = normalize_round
  (* The context's landmark table and the widening-head bracket: a refine
     run through the seam uses the context's own table. *)
  let landmarks_of (rctx : refine_ctx) = rctx.Cbat_runctx.rc_landmarks
  let with_widening_head (rctx : refine_ctx) head f =
    Cbat_landmarks.with_widening_head rctx.Cbat_runctx.rc_landmarks head f
  let refine_edge = refine_edge
  let refine_edge_count_writes = refine_edge_count_writes

  let acquire_unsat ~(rctx : refine_ctx) ~entry env blk disabled =
    Cbat_backward.acquire_unsat ~synth:!(rctx.rc_synth) ~rctx ~entry
      ~landmarks:rctx.Cbat_runctx.rc_landmarks
      ~witness:rctx.rc_nonneg env blk disabled

  (* The walk's env-write sites, named for the counting refine. *)
  type write_site = Cbat_backward.write_site = Output_write | Input_write

  (* The address filter's element-level coverage tests. *)
  let piece_touches_cell = Cbat_backward.piece_touches_cell
  let piece_touches_image = Cbat_backward.piece_touches_image
end
