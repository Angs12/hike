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
open Graphlib.Std

module Stages = Cbat_vsa_stages

module CG = Graphs.Callgraph

module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Mem = Cbat_ai_memmap
module Word_ops = Cbat_word
module Utils = Cbat_vsa_utils

(* WTO over the engine cfg; [succ] supplies the successor function
   (the resolved dispatch's extra edges ride it). *)
let wto_of_cfg ~(succ : tid -> tid list) (cfg : Graphs.Tid.t) :
    Cbat_wto.comp list =
  Cbat_wto.wto
    ~nodes:(Graphs.Tid.nodes cfg |> Seq.to_list)
    ~succ
    ~pred:(fun n -> Graphs.Tid.Node.preds n cfg |> Seq.to_list)


(* Solution still changing at the step cap. *)
exception Fixpoint_not_converged of int * (tid, AI.t) Solution.t
  * (tid * tid) option

type vsa_sol = (tid, AI.t) Solution.t


let default_entry () : AI.t = AI.top

let init_sol ~(abi : Hike_abi.t) ?entry (sub : sub term) =
  let empty_map = Tid.Map.empty in
  let msb = Term.first blk_t sub in
  let entry_state = Option.value ~default:(default_entry ()) entry in
  (* The default entry seeds the SP with the SYMBOLIC SEGMENT BASE:
     every SP-derived address denotes [StackOff]; explicit fixture
     entries keep their own words. *)
  let entry_state =
    match entry with
    | None ->
      AI.add_word entry_state
        ~key:(Var.base abi.Hike_abi.sp)
        ~data:(WordSet.stack_word_i64 0L)
    | Some e -> e in
  let set_init sb = Map.set empty_map ~key:(Term.tid sb) ~data:entry_state in
  let base_map = Option.value_map ~default:empty_map ~f:set_init msb in
  (* A partial CFG is unsound; out-of-graph blocks read bottom. *)
  Solution.create base_map AI.bottom

(* Per-sub def-chain map. *)
let defs_of_sub (s : sub term) : (def term * bool) Var.Map.t =
  Term.enum blk_t s
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.fold ~init:Var.Map.empty ~f:begin fun m d ->
    let key = Var.base (Def.lhs d) in
    match Core.Map.find m key with
    | None -> Core.Map.set m ~key ~data:(d, true)
    | Some _ -> Core.Map.set m ~key ~data:(d, false)
  end

let stores_of_sub (s : sub term) : def term list =
  Term.enum blk_t s
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.filter ~f:(fun d ->
      match Def.rhs d with
      | Bil.Store _ -> true
      | _ -> false)
  |> Seq.to_list

(* Preserved registers: the convention's SP plus its callee-saved GPRs. *)
let preserved_of_sub ~(abi : Hike_abi.t) (s : sub term) : Var.Set.t =
  let regs =
    abi.Hike_abi.sp :: abi.Hike_abi.callee_saved
    |> Var.Set.of_list in
  let virt =
    Term.enum blk_t s
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.fold ~init:Var.Set.empty ~f:begin fun acc d ->
      let acc =
        if Var.is_virtual (Def.lhs d)
        then Core.Set.add acc (Var.base (Def.lhs d)) else acc in
      Exp.free_vars (Def.rhs d)
      |> Core.Set.fold ~init:acc ~f:begin fun acc v ->
        if Var.is_virtual v then Core.Set.add acc (Var.base v) else acc
      end
    end in
  Core.Set.union regs virt


(* Per-sub static edge table: per (block, jmp) accumulated cond, in
   the completed (negation-free) form. *)
let edge_conds_of (sub : sub term) : exp Tid.Map.t Tid.Map.t =
  let ircfg = Sub.to_cfg sub in
  let tbl : (Tid.t, exp Tid.Map.t) Hashtbl.t =
    Hashtbl.create (module Tid) in
  Graphs.Ir.edges ircfg
  |> Seq.iter ~f:(fun e ->
      let src = Graphs.Ir.Node.label (Graphs.Ir.Edge.src e) in
      let jmp = Graphs.Ir.Edge.jmp e in
      let jt = Term.tid jmp in
      let by_jmp =
        Option.value (Hashtbl.find tbl (Term.tid src)) ~default:Tid.Map.empty in
      let by_jmp =
        Core.Map.set by_jmp ~key:jt
          ~data:(Cbat_vsa_utils.complete_cond (Graphs.Ir.Edge.cond e ircfg)) in
      Hashtbl.set tbl ~key:(Term.tid src) ~data:by_jmp);
  Hashtbl.fold tbl ~init:Tid.Map.empty ~f:(fun ~key ~data acc ->
      Core.Map.set acc ~key ~data)

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

(* Per-walk metrics: production builds see only the type and no-op
   stubs below. *)

let rec static_graph_vsa
    ~(abi : Hike_abi.t)
    ?(written : Var.Set.t option Tid.Map.t = Tid.Map.empty)
    ?(resolved : Tid.Set.t Tid.Map.t = Tid.Map.empty)
    (ctx : Program.t) (s : Sub.t) (init : vsa_sol) : vsa_sol =
  let preserved = preserved_of_sub ~abi s in
  let edge_conds = edge_conds_of s in
  let disabled_conds = disabled_conds_of ~edge_conds s in
  let cfg = Sub.to_graph s in
  (* Pseudo-nodes never reach denotation. *)
  let cfg_tmp = Graphs.Tid.Node.remove Graphs.Tid.start cfg
            |> Graphs.Tid.Node.remove Graphs.Tid.exit in
  let rctx = Cbat_runctx.mk_rctx ~cfg:cfg_tmp ~abi s in
  let cfg = cfg_tmp in
  (* The dispatch graph: the CFG plus the Resolved dispatches' extra
     edges, serving the WTO, the worklist, and the predecessor lists. *)
  let dg = Cbat_dispatch_graph.make ~cfg
      ~blocks:(Tid.Set.of_list (Core.Map.keys rctx.Cbat_runctx.rc_blocks))
      resolved s
  in
  let { Cbat_dispatch_graph.succs; Cbat_dispatch_graph.preds } = dg in
  (* WTO fixpoint; inner SCCs stabilize first. *)
  let wto = wto_of_cfg ~succ:succs cfg_tmp in
  let smry = Cbat_wto.summary wto in
  let heads = smry.Cbat_wto.heads in
  let head_to_blocks = smry.Cbat_wto.head_to_blocks in
  let block_to_head = smry.Cbat_wto.block_to_head in
  (* Widen cycle vars per head. *)
  let need_map : Var.Set.t Tid.Map.t =
    let compute_need (blocks : Tid.Set.t) : Var.Set.t =
      let defs =
        Core.Set.to_list blocks
        |> List.concat_map ~f:(fun tid ->
            match Core.Map.find rctx.rc_blocks tid with
            | Some bf -> Term.enum def_t bf.bf_term |> Seq.to_list
            | None -> [])
      in
      let def_vars = Var.Set.of_list (List.map defs ~f:(fun d -> Var.base (Def.lhs d))) in
      if Core.Set.is_empty def_vars then Var.Set.empty
      else begin
        let succ_tbl : (Var.t, Var.t list) Hashtbl.t = Hashtbl.create (module Var) in
        let pred_tbl : (Var.t, Var.t list) Hashtbl.t = Hashtbl.create (module Var) in
        List.iter defs ~f:(fun d ->
          let lhs = Var.base (Def.lhs d) in
          let uses = Exp.free_vars (Def.rhs d) |> Core.Set.to_list |> List.map ~f:Var.base in
          List.iter uses ~f:(fun u ->
            if Core.Set.mem def_vars u then begin
              Hashtbl.add_multi succ_tbl ~key:lhs ~data:u;
              Hashtbl.add_multi pred_tbl ~key:u ~data:lhs
            end));
        let module Var_scc = Cbat_wto.Scc (struct
            type t = Var.t
            let compare = Var.compare
          end) in
        let comps =
          Var_scc.partition (Core.Set.to_list def_vars)
            (Hashtbl.find_multi succ_tbl) (Hashtbl.find_multi pred_tbl) in
        List.fold comps ~init:Var.Set.empty ~f:(fun need comp ->
            match comp with
            | [v] ->
              let succs = Hashtbl.find_multi succ_tbl v in
              if List.mem succs v ~equal:Var.equal then
                Core.Set.add need v
              else need
            | vs when List.length vs > 1 ->
              List.fold vs ~init:need ~f:(fun need v ->
                  Core.Set.add need v)
            | _ -> need)
      end
    in
    Hashtbl.fold head_to_blocks ~init:Tid.Map.empty
      ~f:(fun ~key:h ~data:blocks acc ->
        Core.Map.set acc ~key:h ~data:(compute_need blocks))
  in
  
  let sol_default = Solution.default init in
  (* The walk's signed-row witness: producer-proven non-negativity,
     computed once from the sub's defs and stores. *)
  let defs_tbl = defs_of_sub s in
  let stores_tbl = stores_of_sub s in
  let rctx =
    { rctx with
      Cbat_runctx.rc_nonneg =
        (fun ~env e ->
          Cbat_backward.prove_nonneg ~defs:defs_tbl ~stores:stores_tbl ~env e) } in
  (* The initial solution seeds the store; from here the store is the only
     home for per-block values, versions, and the caches they key. *)
  let rc_cell =
    ref
      (Cbat_runctx.with_sol rctx
         (Solution.enum init
          |> Seq.fold ~init:Tid.Map.empty
               ~f:(fun m (k, v) -> Core.Map.set m ~key:k ~data:(v, 0)))) in
  let get n =
    Option.value_map (Core.Map.find (!rc_cell).rc_state.fs_sol n)
      ~default:sol_default ~f:fst in
  (* Store plus version bump; the stability check below compares first. *)
  let set n v =
    let rc = !rc_cell in
    let st = rc.rc_state in
    let ver =
      Option.value_map (Core.Map.find st.fs_sol n) ~default:1
        ~f:(fun (_, k) -> k + 1) in
    rc_cell :=
      Cbat_runctx.with_sol rc
        (Core.Map.set st.fs_sol ~key:n ~data:(v, ver)) in
  (* The plain solution view of the versioned store. *)
  let mk_sol () =
    Solution.create
      (Core.Map.map (!rc_cell).rc_state.fs_sol ~f:fst)
      sol_default in
  Stages.reset ();
  let total_processed = ref 0 in
  let max_steps = 6000 in
  (* Per-head visit counts; each head gets its own warmup window. *)
  let head_visits : (Tid.t, int) Hashtbl.t = Hashtbl.create (module Tid) in
  let head_warmed (v : Tid.t) : bool =
    Option.value ~default:0 (Hashtbl.find head_visits v) > 10 in
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
      raise (Fixpoint_not_converged (max_steps, sol, None))
    end;
    let old = get v in
    let preds = preds v in
    (* Dead bindings never reach the join; the keep-set depends only on
       the visited block, not on the predecessor. *)
    let keep =
      Option.value_map (Core.Map.find (!rc_cell).rc_blocks v)
        ~default:Var.Set.empty ~f:(fun bf -> bf.bf_live_in)
    in
    (* Snapshot for the deep walk. *)
    let sol_snap = mk_sol () in
    let incoming =
      if List.is_empty preds then old
      else
        let outs = List.map preds ~f:(fun p ->
            let head_opt, p_entry =
              Stages.time `Glue (fun () ->
                let head_opt = Hashtbl.find block_to_head p in
                rctx.Cbat_runctx.rc_landmarks.Cbat_landmarks.widening_at_head <- head_opt;
                let p_entry = get p in
                (head_opt, p_entry)) in

            let rc = !rc_cell in
             let res = Stages.time `Denote (fun () ->
               fst (Cbat_forward.denote_block ~preserved ~written ~resolved
                     ~sub:s ~edge_conds ~disabled:disabled_conds
                     ~sol:sol_snap ~rctx:rc
                     ctx ~source:p p_entry ~target:v)) in
            let res = Stages.time `Glue (fun () -> AI.gc res ~keep) in
            rctx.Cbat_runctx.rc_landmarks.Cbat_landmarks.widening_at_head <- None;
            res) in
        (Stages.time `Join (fun () ->
           Option.value ~default:old (List.reduce outs ~f:AI.join)))
    in
    let new_val =
      if List.is_empty preds then old
      else if Core.Set.mem heads v && head_warmed v then begin
        let j = Stages.time `Join (fun () -> AI.join old incoming) in
        if Stages.time `Equal (fun () -> AI.equal old j)
        then old
        else begin
        (* Finite extrapolates; Zero joins; Inf widens. *)
        let need = Option.value ~default:Var.Set.empty (Core.Map.find need_map v) in
        rctx.Cbat_runctx.rc_landmarks.Cbat_landmarks.widening_at_head <- Some v;
        let res = match Cbat_landmarks.lm_calc_steps rctx.Cbat_runctx.rc_landmarks v with
          | `Finite n ->
            let r = Stages.time `Widen (fun () -> AI.selective_widen_extrapolate ~head:(Some v) ~landmarks:rctx.Cbat_runctx.rc_landmarks ~need ~steps:n old incoming) in
            Cbat_landmarks.clear_head rctx.Cbat_runctx.rc_landmarks v (Hashtbl.find_exn head_to_blocks v);
            r
          | `Zero ->
            Cbat_landmarks.lm_advance rctx.Cbat_runctx.rc_landmarks v;
            j
          | `Inf ->
            Stages.time `Widen (fun () -> AI.widen_join old incoming)
        in
        rctx.Cbat_runctx.rc_landmarks.Cbat_landmarks.widening_at_head <- None;
        res
        end
      end else
        Stages.time `Join (fun () -> AI.join old incoming)
    in
    (* Bump-only-on-change: physical sharing first, then the timed compare. *)
    if phys_equal old new_val
       || Stages.time `Equal (fun () -> AI.equal old new_val)
    then false
    else (Stages.time `Glue (fun () -> set v new_val); true))
  in
  (* The queue pops the lowest WTO position. *)
  let pos (v : Tid.t) : int =
    Option.value ~default:Int.max_value
      (Core.Map.find smry.Cbat_wto.pos_of v) in
  (* Succ-seeded WTO-priority worklist; every visit runs process_vertex
     completely, and changes enqueue Tid-CFG successors. *)
  let pending = ref Tid.Set.empty in
  (* Entry itself is never seeded: init_sol pre-seeds its state. *)
  Option.iter (Term.first blk_t s) ~f:(fun entry ->
    succs (Term.tid entry)
    |> List.iter ~f:(fun t -> pending := Core.Set.add !pending t));
  (* A block that gained an extra-edge predecessor re-joins even from
     a stable warm seed — its incoming set grew without any
     predecessor's value changing. *)
  Core.Set.iter dg.Cbat_dispatch_graph.gained_preds ~f:(fun t ->
      pending := Core.Set.add !pending t);
  let pop_min () =
    let best =
      Core.Set.fold !pending ~init:None ~f:(fun best t ->
          match best with
          | None -> Some t
          | Some b -> if pos t < pos b then Some t else best) in
    match best with
    | None -> None
    | Some v ->
      pending := Core.Set.remove !pending v;
      Some v in
  let rec stabilize_worklist () =
    match pop_min () with
    | None -> ()
    | Some v ->
      if process_vertex v then
        succs v
        |> List.iter ~f:(fun t -> pending := Core.Set.add !pending t);
      stabilize_worklist () in
  stabilize_worklist ();
  Stages.report (Sub.name s);
  mk_sol ()
module Cbat_extraction = struct
(* Classification vocabulary: the (lo,hi) pair is the denotation's
   position interval on the model's ABSOLUTE segment line (see
   [classify]); "below/above the entry RSP" reads as below/above the
   segment base.
   - [Range]/[Infinite]: entirely below the entry RSP — this sub's
     own frame.
   - [Caller]: entirely at/above — ABI-visible caller-window traffic.
   - [Mixed]: two-sided or wrapped — the runtime address is GENUINELY
     either-based; the emitter's rule is the two-base select. *)
(* Re-exported from cbat_clp_set_composite for the seam's consumers. *)
type kind = WordSet.kind =
  | Range of int64 * int64
  | Infinite of int64 * int64
  | Caller of int64 * int64
  | Mixed of int64 * int64
  | Dead

let unbounded_span = Cbat_clp_set_composite.unbounded_span
let is_unbounded_span = Cbat_clp_set_composite.is_unbounded_span
let caller_split = Cbat_clp_set_composite.caller_split
let position_of_offset = Cbat_clp_set_composite.position_of_offset
let classify = Cbat_clp_set_composite.classify
let equal_kind = Cbat_clp_set_composite.equal_kind

(* Address of a stack-access rhs using Exp.visitor. *)
let stack_address_of_rhs (rhs : Bil.exp) : Bil.exp option =
  let vis =
    object
      inherit [ Bil.exp option ] Exp.visitor
      method! visit_load ~mem:_ ~addr _ _ acc =
        Base.Option.first_some acc (Some addr)
      method! visit_store ~mem:_ ~addr ~exp:_ _ _ acc =
        Base.Option.first_some acc (Some addr)
    end
  in
  vis#visit_exp rhs None
end

(* Re-exports for the mli's fixture seam. *)
type refine_ctx = Cbat_runctx.refine_ctx
let mk_rctx ~cfg ~abi = Cbat_runctx.mk_rctx ~cfg ~abi

(* Re-exports of the sibling transfer/forward/backward modules. *)
let set_addr_bits = Cbat_transfer.set_addr_bits

type section_image = Cbat_transfer.section_image = {
  img_lo : int64;
  img_hi : int64;
  img_bytes : Bytes.t;
}

let set_section_images = Cbat_transfer.set_section_images
let with_images = Cbat_transfer.with_images
let denote_def = Cbat_transfer.denote_def
let denote_defs = Cbat_transfer.denote_defs
let denote_imm_exp = Cbat_transfer.denote_imm_exp
let reachable_jumps = Cbat_transfer.reachable_jumps
let fold_block_states = Cbat_transfer.fold_block_states
let last_defs = Cbat_transfer.last_defs

(* [e] denotes in the before-env of [def] — the block's defs replay
   from [pre] up to [def], the target def's own transfer not run — or,
   with no [def], in the block's postcondition.  A [def] outside [blk]
   denotes in [AI.top]. *)
let denote_exp_at :
    pre:AI.t -> blk:blk term -> ?def:def term -> exp ->
    (WordSet.t, Type.error) Result.t =
  fun ~pre ~blk ?def e ->
    match def with
    | None -> denote_imm_exp e (denote_defs blk pre)
    | Some d ->
        let hit = ref false in
        let env =
          Term.enum def_t blk
          |> Seq.fold ~init:pre ~f:(fun env x ->
              if !hit then env
              else if Tid.equal (Term.tid x) (Term.tid d) then (
                hit := true;
                env)
              else denote_def x env)
        in
        if !hit then denote_imm_exp e env else denote_imm_exp e AI.top

(* The per-block boundary envs of a solution: pre is the solution's
   entry state, post the block's def replay from it (the state the
   block's jmps read). *)
let block_envs_of_sol ~(sol : (tid, AI.t) Solution.t) (sub : sub term) :
    (AI.t * AI.t) Tid.Map.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m blk ->
      let pre = Solution.get sol (Term.tid blk) in
      Core.Map.set m ~key:(Term.tid blk) ~data:(pre, denote_defs blk pre))

let constrain_edge = Cbat_backward.constrain_edge
let inverse_denote = Cbat_backward.inverse_denote

(* The seam's seed shape: the cond's leaf constraints as (var, row)
   pairs. *)
let refine_edge ~sol ~rctx ~seeds env blk =
  Cbat_backward.refine_edge ~sol ~rctx
    ~seeds:(List.fold seeds ~init:Var.Map.empty
              ~f:(fun m (v, c) -> Core.Map.set m ~key:(Var.base v) ~data:c))
    env blk

(* The fixtures' construction seam (cbat_vsa.mli's Test_seam). *)
module Test_seam = struct
  type refine_ctx = Cbat_runctx.refine_ctx
  let denote_def = denote_def
  let denote_defs = denote_defs
  let denote_imm_exp = denote_imm_exp
  let fold_block_states = fold_block_states
  let reachable_jumps = reachable_jumps
  let constrain_edge = constrain_edge
  let inverse_denote = inverse_denote
  let mk_rctx = mk_rctx
  let refine_edge = refine_edge
end
