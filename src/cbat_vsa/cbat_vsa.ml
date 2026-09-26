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

(* WTO over the engine cfg; [succ]/[pred] are the dispatch graph's
   accessors — the resolved dispatches' extra edges ride BOTH, so the
   ordering closes on the same graph pair it walks. *)
(* The fixpoint's visit budget: a floor for tiny subs plus a
   per-block allowance, so a sub's sweep count is size-independent. *)
let min_visit_budget = 6000
let visits_per_block = 8
(* A head widens only after this many warmup visits. *)
let head_warmup_visits = 10

let wto_of_cfg ~(succ : tid -> tid list) ~(pred : tid -> tid list)
    (cfg : Graphs.Tid.t) : Cbat_wto.comp list =
  Cbat_wto.wto
    ~nodes:(Graphs.Tid.nodes cfg |> Seq.to_list)
    ~succ ~pred


(* Solution still changing at the step cap. *)
exception Fixpoint_not_converged of int * (tid, AI.t) Solution.t

type vsa_sol = (tid, AI.t) Solution.t


let default_entry () : AI.t = AI.top

(* The sub's entry block: the CFG's [Start] pseudo-node points to it.
   Term order need not put it first (a cold partition can precede it),
   so read the graph, not [Term.first]. *)
let entry_block_of (sub : sub term) : blk term option =
  let cfg = Sub.to_graph sub in
  Graphs.Tid.Node.succs Graphs.Tid.start cfg
  |> Seq.filter ~f:(fun tid -> not (Tid.equal tid Graphs.Tid.exit))
  |> Seq.min_elt ~compare:Tid.compare
  |> Option.bind ~f:(fun tid -> Term.find blk_t sub tid)

let init_sol ~(abi : Hike_abi.t) ?entry (sub : sub term) =
  let empty_map = Tid.Map.empty in
  let msb = entry_block_of sub in
  let entry_state = Option.value ~default:(default_entry ()) entry in
  Cbat_transfer.set_sp_var abi.Hike_abi.sp;
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

(* The run's context: the library builder plus production's own defaults —
   the non-negativity oracle over the sub's defs and stores, and the run's
   sub-address lookup.  The fixpoint and the fixtures' seam build the same
   context through this one builder. *)
let mk_rctx_with_oracle ~(cfg : Graphs.Tid.t) ~(abi : Hike_abi.t)
    ?sub_lookup (s : sub term) : Cbat_runctx.refine_ctx =
  let rctx = Cbat_runctx.mk_rctx ~cfg ~abi ?sub_lookup s in
  let defs = defs_of_sub s in
  let stores = stores_of_sub s in
  (* The stores grouped by their address exp: the witness reads the
     matching group, never every store in the sub. *)
  let store_index =
    Base.List.fold stores ~init:[] ~f:(fun acc d ->
        match Def.rhs d with
        | Bil.Store (_, addr', _, _, _) ->
          (match Base.List.Assoc.find acc addr' ~equal:Exp.equal with
           | Some grp -> Base.List.Assoc.add acc addr' (d :: grp) ~equal:Exp.equal
           | None -> (addr', [ d ]) :: acc)
          | _ -> acc)
  in
  { rctx with
    Cbat_runctx.rc_nonneg =
      (fun ~env e -> Cbat_backward.prove_nonneg ~defs ~index:store_index ~env e) }

(* Preserved registers: the convention's SP plus its callee-saved GPRs. *)
let preserved_of_sub ~(abi : Hike_abi.t) (s : sub term) : Int.Set.t =
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
  Cbat_var_id.intern_set (Core.Set.union regs virt)


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

(* The widen cycle's need set: the block SCC's variable SCCs (a
   singleton variable SCC needs itself iff self-looping; every
   multi-vertex variable SCC needs all its members). *)
let compute_need ~(rc_blocks : Cbat_runctx.block_facts Tid.Map.t)
    (blocks : Tid.Set.t) : Var.Set.t =
  let defs =
    Core.Set.to_list blocks
    |> List.concat_map ~f:(fun tid ->
        match Core.Map.find rc_blocks tid with
        | Some bf -> Term.enum def_t bf.bf_term |> Seq.to_list
        | None -> [])
  in
  let cycle_vars = Var.Set.of_list (List.map defs ~f:(fun d -> Var.base (Def.lhs d))) in
  if Core.Set.is_empty cycle_vars then Var.Set.empty
  else begin
    let succ_tbl : (Var.t, Var.t list) Hashtbl.t = Hashtbl.create (module Var) in
    let pred_tbl : (Var.t, Var.t list) Hashtbl.t = Hashtbl.create (module Var) in
    List.iter defs ~f:(fun d ->
      let lhs = Var.base (Def.lhs d) in
      let uses = Exp.free_vars (Def.rhs d) |> Core.Set.to_list |> List.map ~f:Var.base in
      List.iter uses ~f:(fun u ->
        if Core.Set.mem cycle_vars u then begin
          Hashtbl.add_multi succ_tbl ~key:lhs ~data:u;
          Hashtbl.add_multi pred_tbl ~key:u ~data:lhs
        end));
    let module Var_scc = Cbat_wto.Scc (struct
        type t = Var.t
      end) in
    let comps =
      Var_scc.partition (Core.Set.to_list cycle_vars)
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

(* The round-down idiom [(x >> k) << k] with a literal k is the mask
   [x & ~(2^k - 1)]; the mask form computes exactly on a stack-symbolic
   operand, while the shifts alone read the base's unknown bits and
   answer top.  At -O0 the idiom spans two defs ([v := x >> k] then
   [v := v << k]) — the pair rewrites to the mask on the first def and
   the identity copy on the second. *)
let normalize_round (s : Sub.t) : Sub.t =
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
  let pairs =
    Term.enum blk_t s
    |> Seq.concat_map ~f:(fun blk ->
        let rec walk = function
          | d1 :: d2 :: rest -> (
              match (Def.rhs d1, Def.rhs d2) with
              | ( Bil.BinOp (Bil.RSHIFT, x, Bil.Int k),
                  Bil.BinOp (Bil.LSHIFT, Bil.Var v, Bil.Int j) )
                when Var.equal v (Def.lhs d1)
                     && Var.equal (Def.lhs d2) (Def.lhs d1)
                     && Word.equal k j -> (
                  let w =
                    match x with
                    | Bil.Var v -> (
                        match Var.typ v with Type.Imm n -> n | _ -> 64)
                    | _ -> 64
                  in
                  match mask_of k w with
                  | Some mask ->
                    (Term.tid d1, Bil.BinOp (Bil.AND, x, Bil.Int mask))
                    :: (Term.tid d2, Bil.Var (Def.lhs d1))
                    :: walk rest
                  | None -> walk rest)
              | _ -> walk rest)
          | _ -> []
        in
        walk (Term.enum def_t blk |> Seq.to_list) |> Seq.of_list)
    |> Seq.fold ~init:Tid.Map.empty
         ~f:(fun m (t, r) -> Map.set m ~key:t ~data:r)
  in
  if Map.is_empty pairs then s
  else
    Term.map blk_t s ~f:(fun blk ->
        Term.map def_t blk ~f:(fun d ->
            match Map.find pairs (Term.tid d) with
            | Some r -> Def.with_rhs d r
            | None -> d))

let rec static_graph_vsa
    ~(abi : Hike_abi.t)
    ?(written : Int.Set.t option Tid.Map.t = Tid.Map.empty)
    ?(resolved : Tid.Set.t Tid.Map.t = Tid.Map.empty)
    ?(sub_lookup : int64 -> Tid.t option = fun _ -> None)
    (ctx : Program.t) (s : Sub.t) (init : vsa_sol) : vsa_sol =
  let s = normalize_round s in
  let preserved = preserved_of_sub ~abi s in
  let edge_conds = edge_conds_of s in
  let disabled_conds = disabled_conds_of ~edge_conds s in
  let cfg = Sub.to_graph s in
  (* Pseudo-nodes never reach denotation. *)
  let cfg_tmp = Graphs.Tid.Node.remove Graphs.Tid.start cfg
            |> Graphs.Tid.Node.remove Graphs.Tid.exit in
  let rctx = mk_rctx_with_oracle ~cfg:cfg_tmp ~abi ~sub_lookup s in
  let cfg = cfg_tmp in
  (* The dispatch graph: the CFG plus the Resolved dispatches' extra
     edges, serving the WTO, the worklist, and the predecessor lists. *)
  let dg = Cbat_dispatch_graph.make ~cfg
      ~blocks:(Tid.Set.of_list (Core.Map.keys rctx.Cbat_runctx.rc_blocks))
      resolved s
  in
  let { Cbat_dispatch_graph.succs; Cbat_dispatch_graph.preds } = dg in
  (* WTO fixpoint; inner SCCs stabilize first. *)
  let wto = wto_of_cfg ~succ:succs ~pred:preds cfg_tmp in
  let smry = Cbat_wto.summary wto in
  let heads = smry.Cbat_wto.heads in
  let head_to_blocks = smry.Cbat_wto.head_to_blocks in
  let block_to_head = smry.Cbat_wto.block_to_head in
  let need_map : Core.Int.Set.t Tid.Map.t =
    Hashtbl.fold head_to_blocks ~init:Tid.Map.empty
      ~f:(fun ~key:h ~data:blocks acc ->
        Core.Map.set acc ~key:h ~data:(Cbat_var_id.intern_set (compute_need ~rc_blocks:rctx.rc_blocks blocks)))
  in
  
  let sol_default = Solution.default init in
  (* The initial solution seeds the store; from here the store is the only
     home for per-block values, versions, and the caches they key. *)
  let rc_cell =
    ref
      (Cbat_runctx.with_sol rctx
         (Solution.enum init
          |> Seq.fold ~init:Tid.Map.empty
               ~f:(fun m (k, v) -> Core.Map.set m ~key:k ~data:v))) in
  let get n =
    Option.value (Core.Map.find (!rc_cell).rc_state.fs_sol n) ~default:sol_default in
  let set n v =
    let rc = !rc_cell in
    rc_cell :=
      Cbat_runctx.with_sol rc
        (Core.Map.set rc.rc_state.fs_sol ~key:n ~data:v) in
  let mk_sol () =
    Solution.create (!rc_cell).rc_state.fs_sol sol_default in
  Stages.reset ();
  let total_processed = ref 0 in
  (* The visit budget scales with the block count so a sub's sweep
     allowance is size-independent; the floor bounds tiny subs. *)
  let max_steps =
    Stdlib.max min_visit_budget
      (visits_per_block * Core.Map.length rctx.rc_blocks) in
  (* Per-head visit counts; each head gets its own warmup window. *)
  let head_visits : (Tid.t, int) Hashtbl.t = Hashtbl.create (module Tid) in
  let head_warmed (v : Tid.t) : bool =
    Option.value ~default:0 (Hashtbl.find head_visits v)
    > head_warmup_visits in
#ifdef VSA_DEBUG
  (* Forward witness: every guard cond from [p] to [v] denotates false on
     the pred's entry state, so the edge is dead without the backward
     refinement.  A dispatch extra-edge has no jmp and cannot be
     witnessed. *)
  let edge_forward_dead ~(p : Tid.t) ~(v : Tid.t) : bool =
    match Core.Map.find (!rc_cell).rc_blocks p with
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
              match Cbat_transfer.denote_imm_exp cond (get p) with
              | Ok w -> not (WordSet.elem Cbat_word.b1 w)
              | Error _ -> false))
  in
#endif
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
    let old = get v in
    let preds = preds v in
    (* Dead bindings never reach the join; the keep-set depends only on
       the visited block, not on the predecessor. *)
    let keep =
      Option.value_map (Core.Map.find (!rc_cell).rc_blocks v)
        ~default:Int.Set.empty ~f:(fun bf -> bf.bf_live_ids)
    in
    let incoming =
      if List.is_empty preds then old
      else
        let outs = List.map preds ~f:(fun p ->
            Cbat_landmarks.with_widening_head rctx.Cbat_runctx.rc_landmarks
              (Hashtbl.find block_to_head p) (fun () ->
#ifdef VSA_DEBUG
                Cbat_attr_census.bump "bottomskip.edge.total";
#endif
                let p_entry = Stages.time `Glue (fun () -> get p) in
                let rc = !rc_cell in
                let res = Stages.time `Denote (fun () ->
                  Cbat_forward.denote_block ~preserved ~written ~resolved
                        ~edge_conds ~disabled:disabled_conds
                        ~rctx:rc
                        ctx ~source:p p_entry ~target:v) in
                let res = Stages.time `Glue (fun () -> AI.gc res ~keep) in
#ifdef VSA_DEBUG
                (if AI.equal res AI.bottom then begin
                   Cbat_attr_census.bump "bottomskip.edge.bottom";
                   if edge_forward_dead ~p ~v then
                     Cbat_attr_census.bump "bottomskip.edge.forward_dead"
                   else Cbat_attr_census.bump "bottomskip.edge.refine_only"
                 end);
#endif
                res)) in
        (Stages.time `Join (fun () ->
           Option.value ~default:old (List.reduce outs ~f:AI.join)))
    in
#ifdef VSA_DEBUG
    (if not (List.is_empty preds) then
       Cbat_attr_census.bump "bottomskip.entry.total");
    (if AI.equal incoming AI.bottom && not (List.is_empty preds) then begin
       Cbat_attr_census.bump "bottomskip.entry.bottom";
       if List.for_all preds ~f:(fun p -> edge_forward_dead ~p ~v) then
         Cbat_attr_census.bump "bottomskip.entry.forward_dead"
       else Cbat_attr_census.bump "bottomskip.entry.refine_only"
     end);
#endif
    let new_val =
      if List.is_empty preds then old
      else if Core.Set.mem heads v && head_warmed v then begin
        let j = Stages.time `Join (fun () -> AI.join old incoming) in
        if Stages.time `Equal (fun () -> AI.equal old j)
        then old
        else begin
        (* Finite extrapolates; Zero joins; Inf widens. *)
        let need = Option.value ~default:Core.Int.Set.empty (Core.Map.find need_map v) in
        Cbat_landmarks.with_widening_head rctx.Cbat_runctx.rc_landmarks (Some v)
          (fun () ->
            match Cbat_landmarks.lm_calc_steps rctx.Cbat_runctx.rc_landmarks v with
            | `Finite n ->
              let r = Stages.time `Widen (fun () -> AI.selective_widen_extrapolate ~head:v ~landmarks:rctx.Cbat_runctx.rc_landmarks ~need ~steps:n old incoming) in
              Cbat_landmarks.clear_head rctx.Cbat_runctx.rc_landmarks v (Hashtbl.find_exn head_to_blocks v);
              r
            | `Zero ->
              Cbat_landmarks.lm_advance rctx.Cbat_runctx.rc_landmarks v;
              j
            | `Inf ->
              if Cbat_landmarks.cell_driven rctx.Cbat_runctx.rc_landmarks v then
                (* No word landmarks at the head; the memory arm runs the
                   cells' own three-way. Negative steps widen the words. *)
                Stages.time `Widen (fun () ->
                    AI.selective_widen_extrapolate ~head:v
                      ~landmarks:rctx.Cbat_runctx.rc_landmarks ~need ~steps:(-1)
                      old incoming)
              else
                Stages.time `Widen (fun () -> AI.widen_join old incoming))
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
  (* WTO-priority buckets: pos -> the blocks at that position.  A
     block's position is static, so enqueue is one bucket insert and
     pop_min reads the least non-empty bucket. *)
  let pending : Tid.Set.t Int.Map.t ref = ref Int.Map.empty in
  let enqueue t =
    pending :=
      Core.Map.update !pending (pos t) ~f:(function
          | None -> Core.Set.singleton (module Tid) t
          | Some set -> Core.Set.add set t)
  in
  (* Entry itself is never seeded: init_sol pre-seeds its state. *)
  Option.iter (entry_block_of s) ~f:(fun entry ->
    succs (Term.tid entry)
    |> List.iter ~f:enqueue);
  (* A block that gained an extra-edge predecessor re-joins even from
     a stable warm seed — its incoming set grew without any
     predecessor's value changing. *)
  Core.Set.iter dg.Cbat_dispatch_graph.gained_preds ~f:enqueue;
  let pop_min () =
    match Core.Map.min_elt !pending with
    | None -> None
    | Some (p, set) ->
      let v = Core.Set.choose_exn set in
      let rest = Core.Set.remove set v in
      pending :=
        (if Core.Set.is_empty rest then Core.Map.remove !pending p
         else Core.Map.set !pending ~key:p ~data:rest);
      Some v in
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
(* The classification vocabulary lives in Cbat_extraction (re-exported
   so the seam's consumers keep their paths). *)
module Cbat_extraction = Cbat_extraction

(* Re-exports for the mli's fixture seam. *)
type refine_ctx = Cbat_runctx.refine_ctx

(* Re-exports of the sibling transfer/forward/backward modules. *)
let set_addr_bits = Cbat_transfer.set_addr_bits
let set_sp_var = Cbat_transfer.set_sp_var

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

(* The Env Tag seam (the KB domain/slot, the stamp, the raw replay,
   the VSA_DEBUG differential, [denote_exp_at], and the env stamp)
   lives in Cbat_env_tag; re-exported so the consumers keep their
   [Vsa.*] paths. *)
module Env_tag = Cbat_env_tag
let denote_exp_at = Cbat_env_tag.denote_exp_at
let stamp_envs_of_sol = Cbat_env_tag.stamp_envs_of_sol
let env_tag = Cbat_env_tag.env_tag
let set_env_tag = Cbat_env_tag.set_env_tag
let solve_denote = Cbat_env_tag.solve_denote

(* The seam's seed shape: the cond's leaf constraints as (var, constraint)
   pairs. *)
let refine_edge ~sol ~rctx ~seeds env blk =
  (* The walked block's IN state is its entry in [sol]. *)
  Cbat_backward.refine_edge
    ~entry:(Solution.get sol (Term.tid blk))
    ~rctx
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
  let constrain_edge = Cbat_backward.constrain_edge
  let constrain_operands = Cbat_backward.constrain_operands
  let mk_rctx = mk_rctx_with_oracle
  let normalize_round = normalize_round
  (* The context's landmark table and the widening-head bracket: a refine
     run through the seam uses the context's own table. *)
  let landmarks_of (rctx : refine_ctx) = rctx.Cbat_runctx.rc_landmarks
  let with_widening_head (rctx : refine_ctx) head f =
    Cbat_landmarks.with_widening_head rctx.Cbat_runctx.rc_landmarks head f
  let refine_edge = refine_edge
end
