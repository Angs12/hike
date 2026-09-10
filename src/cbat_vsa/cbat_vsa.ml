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

include Core_kernel
open Bap.Std
open Graphlib.Std
module Abi = Hike_abi

module Stages = Cbat_vsa_stages

module CG = Graphs.Callgraph
module CFG = Graphs.Tid

module AI = Cbat_ai_representation
module WordSet = Cbat_clp_set_composite
module Mem = Cbat_ai_memmap
module Word_ops = Cbat_word
module Utils = Cbat_vsa_utils

(* WTO over the engine cfg; swapped accessors reverse it. *)

let wto_of_cfg (cfg : Graphs.Tid.t) : Cbat_wto.comp list =
  Cbat_wto.wto
    ~nodes:(Graphs.Tid.nodes cfg |> Seq.to_list)
    ~succ:(fun n -> Graphs.Tid.Node.succs n cfg |> Seq.to_list)
    ~pred:(fun n -> Graphs.Tid.Node.preds n cfg |> Seq.to_list)


(* Solution still changing at the step cap. *)
exception Fixpoint_not_converged of int * (tid, AI.t) Solution.t
  * (tid * tid) option

type vsa_sol = (tid, AI.t) Solution.t


(* Entry state is top. *)
let default_entry () : AI.t = AI.top

(* Initial solution of a sub. *)
let init_sol ?entry (sub : sub term) =
  let empty_map = Tid.Map.empty in
  let msb = Term.first blk_t sub in
  let entry_state = Option.value ~default:(default_entry ()) entry in
  (* The default entry seeds RSP's word with the SYMBOLIC SEGMENT BASE
     (T3): every SP-derived address denotes [StackOff] — exact offsets
     for tagging and cell keying, a segment-smeared hull for guards (the
     L1 fake-bits pruning class is structurally dead; [value_env] is
     deleted).  Explicit (fixture) entries keep their own words — a
     fixture may choose a concrete RSP universe; the frame relation the
     old rebind clobbered is gone, so nothing else is lost. *)
  let entry_state =
    match entry with
    | None ->
      AI.add_word entry_state
        ~key:(Var.base Abi.x86_64_sysv.sp)
        ~data:(WordSet.stack_word_i64 0L)
    | Some e -> e in
  let set_init sb = Map.set empty_map ~key:(Term.tid sb) ~data:entry_state in
  let base_map = Option.value_map ~default:empty_map ~f:set_init msb in
  (* Partial CFGs give unsound results. *)
  Solution.create base_map AI.bottom

(* Calls abstract; recursion is fallback. *)

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

(* Per-sub store list. *)
let stores_of_sub (s : sub term) : def term list =
  Term.enum blk_t s
  |> Seq.concat_map ~f:(Term.enum def_t)
  |> Seq.filter ~f:begin fun d ->
    match Def.rhs d with
    | Bil.Store _ -> true
    | _ -> false
  end
  |> Seq.to_list

(* Preserved registers. *)
let preserved_of_sub (s : sub term) : Var.Set.t =
  let regs =
    Abi.x86_64_sysv.sp :: Abi.x86_64_sysv.callee_saved
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


(* Per-sub static edge table: per (block, jmp) accumulated cond. *)
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
        match Hashtbl.find tbl (Term.tid src) with
        | None -> Tid.Map.empty
        | Some m -> m in
      let by_jmp =
        Core.Map.set by_jmp ~key:jt
          ~data:(Graphs.Ir.Edge.cond e ircfg) in
      Hashtbl.set tbl ~key:(Term.tid src) ~data:by_jmp);
  Hashtbl.fold tbl ~init:Tid.Map.empty ~f:(fun ~key ~data acc ->
      Core.Map.set acc ~key ~data)

(* Candidate-1 overlap census: per-walk records (guard block, jmp, seed
   mix, visited-block set). Production builds see only the type and
   no-op stubs below — nothing is compiled in (principle #6). *)

let rec static_graph_vsa (stack : tid list) (ctx : Program.t) (s : Sub.t) (init : vsa_sol) : vsa_sol =
  (* Per-sub sets computed once; the walks are un-gated (spec §2.1). *)
  let preserved = preserved_of_sub s in
  (* Per-sub def-chain map. *)
  let defs = defs_of_sub s in
  (* Store list computed once. *)
  let stores = stores_of_sub s in
  (* Frame facts computed once. *)
  (* Per-sub static edge table. *)
  let edge_conds = edge_conds_of s in
  let cfg = Sub.to_graph s in
  (* Pseudo-nodes never reach denotation. *)
  let cfg_tmp = Graphs.Tid.Node.remove Graphs.Tid.start cfg
            |> Graphs.Tid.Node.remove Graphs.Tid.exit in
  (* Run context built once per run. *)
  let rctx = Cbat_runctx.mk_rctx ~cfg:cfg_tmp s in
  (* WTO fixpoint; inner SCCs stabilize first. *)
  let wto = wto_of_cfg cfg_tmp in
  let heads = Cbat_wto.heads_of_comps wto in
  let cfg = cfg_tmp in
  (* Static predecessor lists; process_vertex reads these instead of
     re-deriving them on every visit. *)
  let preds_of =
    Graphs.Tid.nodes cfg
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m v ->
        Core.Map.set m ~key:v
          ~data:(CFG.Node.preds v cfg |> Seq.to_list))
  in
  Cbat_landmarks.clear ();
  let head_to_blocks : (Tid.t, Tid.Set.t) Hashtbl.t = Hashtbl.create (module Tid) in
  let rec collect_heads comps =
    List.iter comps ~f:(function
      | Cbat_wto.Vertex _ -> ()
      | Cbat_wto.SCC (h, inner) ->
        let blocks = Tid.Set.of_list (h :: Cbat_wto.flatten_comps inner) in
        Hashtbl.set head_to_blocks ~key:h ~data:blocks;
        collect_heads inner)
  in
  collect_heads wto;
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

  (* Widen cycle vars per head; folds the single walk above, no second table. *)
  let need_map : Var.Set.t Tid.Map.t =
    let compute_need (blocks : Tid.Set.t) : Var.Set.t =
      (* Every def in the cycle is tracked (spec §2.1). *)
      let defs =
        Core.Set.to_list blocks
        |> List.concat_map ~f:(fun tid ->
            match Core.Map.find rctx.rc_blocks tid with
            | Some blk -> Term.enum def_t blk |> Seq.to_list
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
  (* The initial solution seeds the store; from here the store is the only
     home for per-block values, versions, and the caches they key. *)
  let rc_cell =
    ref
      (Cbat_runctx.with_sol rctx
         (Solution.enum init
          |> Seq.fold ~init:Tid.Map.empty
               ~f:(fun m (k, v) -> Core.Map.set m ~key:k ~data:v))) in
  let get n =
    match Core.Map.find (!rc_cell).rc_state.fs_sol n with
    | Some v -> v
    | None -> sol_default in
  (* Store plus version bump; the stability check below compares first. *)
  let set n v =
    let rc = !rc_cell in
    let st = rc.rc_state in
    let versions =
      match Core.Map.find st.fs_versions n with
      | None -> Core.Map.set st.fs_versions ~key:n ~data:1
      | Some k -> Core.Map.set st.fs_versions ~key:n ~data:(k + 1) in
    rc_cell :=
      Cbat_runctx.with_sol ~versions:(Some versions) rc
        (Core.Map.set st.fs_sol ~key:n ~data:v) in
  Stages.reset ();
  let total_processed = ref 0 in
  let max_steps = 6000 in
  (* Per-head visit counts; each head gets its own warmup window. *)
  let head_visits : (Tid.t, int) Hashtbl.t = Hashtbl.create (module Tid) in
  let head_warmed (v : Tid.t) : bool =
    Option.value ~default:0 (Hashtbl.find head_visits v) > 10 in
  let process_vertex (v : Tid.t) : bool =
    (* Scaffold times engine glue. *)
    Stages.time `Scaffold (fun () ->
    incr total_processed;
    (* This visit counts toward the head's own window, including itself. *)
    if Core.Set.mem heads v then begin
      let n = Option.value ~default:0 (Hashtbl.find head_visits v) in
      Hashtbl.set head_visits ~key:v ~data:(n + 1)
    end;
    if !total_processed > max_steps then begin
      let sol = Solution.create (!rc_cell).rc_state.fs_sol sol_default in
      raise (Fixpoint_not_converged (max_steps, sol, None))
    end;
    let old = get v in
    let preds =
      Core.Map.find preds_of v |> Option.value ~default:[]
    in
    (* Dead bindings never reach the join; the keep-set depends only on
       the visited block, not on the predecessor. *)
    let keep =
      Option.value ~default:Var.Set.empty
        (Core.Map.find (!rc_cell).rc_live_in v)
    in
    (* Snapshot for the deep walk. *)
    let sol_snap = Solution.create (!rc_cell).rc_state.fs_sol sol_default in
    let incoming =
      if List.is_empty preds then old
      else
        let outs = List.map preds ~f:(fun p ->
            (* Per-pred glue. *)
            let head_opt, p_entry =
              Stages.time `Glue (fun () ->
                let head_opt = Hashtbl.find block_to_head p in
                Cbat_landmarks.widening_at_head := head_opt;
                let p_entry = get p in
                (head_opt, p_entry)) in
            
            (* Context threads through transfers. *)
            let rc = !rc_cell in
             let res = Stages.time `Denote (fun () ->
               fst (Cbat_walk.denote_block_with_stores ~preserved ~defs
                     ~stores ~sub:(Some s) ~edge_conds:(Some edge_conds)
                     ~sol:(Some sol_snap) ~rctx:rc
                     ctx ~source:p p_entry ~target:v)) in
            let res = Stages.time `Glue (fun () -> AI.gc res ~keep) in
            Cbat_landmarks.widening_at_head := None;
            res) in
        (Stages.time `Join (fun () ->
           match List.reduce outs ~f:AI.join with
           | Some j -> j
           | None -> old))
    in
    let new_val =
      if List.is_empty preds then old
      else if Core.Set.mem heads v && head_warmed v then begin
        (* Stable heads skip side effects. *)
        (* Join computed once. *)
        let j = Stages.time `Join (fun () -> AI.join old incoming) in
        if Stages.time `Equal (fun () -> AI.equal old j)
        then old
        else begin
        (* Finite extrapolates; Zero joins; Inf widens. *)
        let need = Option.value ~default:Var.Set.empty (Core.Map.find need_map v) in
        Cbat_landmarks.widening_at_head := Some v;
        let res = match Cbat_landmarks.lm_calc_steps v with
          | `Finite n ->
            let r = Stages.time `Widen (fun () -> AI.selective_widen_extrapolate ~head:(Some v) ~need ~steps:n old incoming) in
            Cbat_landmarks.clear_head v (Hashtbl.find_exn head_to_blocks v);
            r
          | `Zero ->
            Cbat_landmarks.lm_advance v;
            j
          | `Inf ->
            Stages.time `Widen (fun () -> AI.widen_join old incoming)
        in
        Cbat_landmarks.widening_at_head := None;
        res
        end
      end else
        (* Non-heads join once. *)
        Stages.time `Join (fun () -> AI.join old incoming)
    in
    (* Bump-only-on-change: physical sharing first, then the timed compare. *)
    if phys_equal old new_val
       || Stages.time `Equal (fun () -> AI.equal old new_val)
    then false
    else (Stages.time `Glue (fun () -> set v new_val); true))
  in
  (* WTO position index built once; the queue pops the lowest. *)
  let pos_of =
    List.mapi (Cbat_wto.flatten_comps wto) ~f:(fun i t -> (t, i))
    |> List.fold ~init:Tid.Map.empty ~f:(fun m (t, i) ->
        Core.Map.set m ~key:t ~data:i) in
  let pos (v : Tid.t) : int =
    Option.value ~default:Int.max_value (Core.Map.find pos_of v) in
  (* One walk-pop allowance for the whole run. *)
  let allowance =
    Core.Map.fold rctx.rc_out_edges ~init:0
      ~f:(fun ~key:_ ~data:n acc -> acc + n) in
  rctx.rc_walk_budget := Cbat_runctx.budget_per_edge * allowance;
  (* Succ-seeded WTO-priority worklist; every visit runs process_vertex
     completely, and changes enqueue Tid-CFG successors. *)
  let pending = ref Tid.Set.empty in
  (* Entry itself is never seeded: init_sol pre-seeds its state. *)
  (match Term.first blk_t s with
  | None -> ()
  | Some entry ->
    Graphs.Tid.Node.succs (Term.tid entry) cfg
    |> Seq.iter ~f:(fun t -> pending := Core.Set.add !pending t));
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
        Graphs.Tid.Node.succs v cfg
        |> Seq.iter ~f:(fun t -> pending := Core.Set.add !pending t);
      stabilize_worklist () in
  stabilize_worklist ();
  Stages.report (Sub.name s);
  Solution.create (!rc_cell).rc_state.fs_sol sol_default
module Cbat_extraction = struct
(* Classification vocabulary.  [Caller] is the producer's lane split
   (D1): a bounded span entirely at/above the entry RSP is ABI-visible
   caller-window traffic (incoming stack args, the return-address
   slot) — the emitter routes it through the hike_stack lane; Range/
   Infinite (spans reaching below the entry RSP, including mixed) are
   this sub's frame lane. *)
type kind =
  | Range of int64 * int64
  | Infinite of int64 * int64
  | Caller of int64 * int64
  | Unbounded
  | Dead
  | VLA of Tid.t
[@@deriving equal]

(* The own/caller split: positives become Caller. *)
let caller_split (k : kind) : kind =
  match k with
  | Range (lo, hi) when Stdlib.Int64.compare lo 0L >= 0 -> Caller (lo, hi)
  | Infinite (lo, hi) when Stdlib.Int64.compare lo 0L >= 0 -> Caller (lo, hi)
  | Range _ | Infinite _ | Caller _ | Unbounded | Dead | VLA _ -> k

(* The offset-space twin of a stack denotation (the tag universe);
   identity for non-stack values is NOT sound (a foreign address would
   masquerade as an offset), so None stays None and callers take their
   sound arm. *)
let relativize_opt (ws : WordSet.t) : WordSet.t option =
  WordSet.relativize ws

(* Kind of a word set. *)
let classify ?vla_tid (ws : WordSet.t) : kind option =
  if WordSet.is_top ws then Some Unbounded
  else if WordSet.is_bottom ws then Some Dead
  else
    match WordSet.min_elem ws, WordSet.max_elem ws with
    | Some lo, Some hi ->
      (match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
       | Ok lo, Ok hi ->
         let is_inf = WordSet.is_infinite ws || Stdlib.Int64.compare lo hi > 0 in
         if is_inf && Option.is_some vla_tid then
           Some (VLA (Option.value_exn vla_tid))
         else if is_inf then Some (Infinite (lo, hi))
         else Some (Range (lo, hi))
       | _ -> Some Unbounded)
    | _ -> Some Unbounded

(* Signed bounds or None. *)
let bounds_of (ws : WordSet.t) : (int64 * int64) option =
  if WordSet.is_top ws || WordSet.is_bottom ws then None
  else
    match WordSet.min_elem ws, WordSet.max_elem ws with
    | Some lo, Some hi -> (
        match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
        | Ok lo, Ok hi -> Some (lo, hi)
        | _ -> None)
    | _ -> None

(* Displacement from the current RSP at the def; None when either side is
   unbounded.  Internal to the escape analysis — never a tag. *)
let sp_displacement (ws : WordSet.t) (rsp_ws : WordSet.t) :
    (int64 * int64) option =
  match bounds_of ws, bounds_of rsp_ws with
  | Some (alo, ahi), Some (rlo, rhi) ->
      Some (Stdlib.Int64.sub alo rhi, Stdlib.Int64.sub ahi rlo)
  | _ -> None

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


let st_tag_of ~(tags : (tid, AI.t) Solution.t) (blk : blk term)
    (addr' : exp) (st_before : AI.t) : AI.t =
  Exp.free_vars addr'
  |> Core.Set.fold ~init:st_before ~f:(fun acc v ->
      match Var.typ v with
      | Type.Imm w ->
        let tag_v = AI.find_word w
            (Solution.get tags (Term.tid blk)) v in
        let cur = AI.find_word w acc v in
        let mm = WordSet.meet cur tag_v in
        if Cbat_word.is_zero (WordSet.cardinality mm)
           || WordSet.equal mm cur
        then acc
        else AI.add_word acc ~key:v ~data:mm
      | Type.Mem _ | Type.Unk -> acc)


(* The ONE stack-access predicate (T3): the address's denotation is a
   stack-symbolic set — the symbolic segment base propagates from the
   seeded entry RSP through arithmetic and memory round-trips (the
   reloaded-pointer channel is structural: spilled RSP-derived values
   are [StackOff] cells), or a bounded plain hull inside the
   non-canonical band (the degraded arm: a bitwise-mangled SP lane).
   A bottom denotation is a dead path — seeding records the Dead kind.
   Non-seeding is sound (the access stays untagged, the real-address
   lane). *)
let is_stack_access (st_before : AI.t) (addr : exp) : bool =
  match Cbat_transfer.denote_imm_exp addr st_before with
  | Error _ -> false
  | Ok ws ->
    if WordSet.is_bottom ws then true
    else WordSet.in_stack_segment ws


(* Outgoing-arg stores: stack writes at or above the current RSP but below
   entry RSP — the pushed-arg signature.  Escape-analysis input computed
   where the per-def state lives; NOT part of the tag product. *)
let outgoing_arg_stores ~(sp : var) ~(sol : (tid, AI.t) Solution.t)
    (sub : sub term) : Tid.Set.t =
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Set.empty ~f:(fun acc blk ->
      let st0 = Solution.get sol (Term.tid blk) in
      let _, acc =
        Base.List.fold_left (Term.enum def_t blk |> Seq.to_list)
          ~init:(st0, acc)
          ~f:(fun (st, acc) d ->
              let st_before = st in
              let st = Cbat_transfer.denote_def d st in
              match stack_address_of_rhs (Def.rhs d) with
              | Some addr when is_stack_access st_before addr ->
                  let st_tag = st_tag_of ~tags:sol blk addr st_before in
                  let acc =
                    match Cbat_transfer.denote_imm_exp addr st_tag with
                    | Ok ws -> (
                        match relativize_opt ws with
                        | Some rel ->
                          (match classify rel, bounds_of rel with
                           | Some (Range (lo, _)), Some _ ->
                             let below_entry = Int64.compare lo 0L < 0 in
                             let above_cur =
                               match sp_displacement rel
                                         (Option.value ~default:ws
                                            (relativize_opt (AI.find_word 64 st_before sp))) with
                               | Some (klo, _) -> Int64.compare klo 0L >= 0
                               | None -> false
                             in
                             if below_entry && above_cur
                             then Core.Set.add acc (Term.tid d) else acc
                           | _ -> acc)
                        | None -> acc)
                    | Error _ -> acc
                  in
                  (st, acc)
              | _ -> (st, acc))
      in
      acc)


let rec extract ~(dynamic_alloc : def term -> bool)
    ~(alloc_tids : Tid.Set.t)
    ~(sol : (tid, AI.t) Solution.t)
    (sub : sub term) :
    kind Tid.Map.t =
  let tags = sol in
  let raw =
    Term.enum blk_t sub
    |> Seq.fold ~init:[] ~f:(fun acc blk ->
        (* Every def is denoted; seeding replaces the tag match. *)
        let defs = Term.enum def_t blk |> Seq.to_list in
        let _, acc =
          Base.List.fold_left defs
            ~init:(Solution.get tags (Term.tid blk), acc)
            ~f:(fun (st, acc) d ->
                 let st_before = st in
                 let st = Cbat_transfer.denote_def d st in
                 match stack_address_of_rhs (Def.rhs d) with
                 | Some addr when is_stack_access st_before addr ->
                     (* Addresses use tag-state values; the tag is the
                        SEGMENT-RELATIVE offset set (the denotation's
                        offset-space twin). *)
                     let st_tag = st_tag_of ~tags blk addr st_before in
                     (match Cbat_transfer.denote_imm_exp addr st_tag with
                      | Ok ws ->
                          let ws =
                            match relativize_opt ws with
                            | Some rel -> rel
                            | None -> ws in
                          (match classify ws with
                           | Some kind ->
                               let acc = (Term.tid d, kind, ws) :: acc in
                               (st, acc)
                           | None ->
                               let ws = WordSet.top 64 in
                               let acc = (Term.tid d, Unbounded, ws) :: acc in
                               (st, acc))
                      | Error _ ->
                          let ws = WordSet.top 64 in
                          let acc = (Term.tid d, Unbounded, ws) :: acc in
                          (st, acc))
                 | _ -> (st, acc))
        in
        acc)
  in
  let raw = List.rev raw in
  (* Overlapping addresses merge. *)
  let span_of = function
    | Range (lo, hi) -> (lo, hi)
    | Infinite (lo, hi) -> (Stdlib.Int64.min lo hi, Stdlib.Int64.max lo hi)
    | Caller (lo, hi) -> (lo, hi)
    | Unbounded | Dead | VLA _ -> (0L, 0L)
  in
  let merged_tags : kind Tid.Map.t =
    let bounded, unbounded_or_dead =
      Base.List.partition_tf raw ~f:(fun (_, kind, _) ->
          match kind with
          | Range _ -> true
          | Infinite _ | Caller _ | Unbounded | Dead | VLA _ -> false)
    in
    let items = bounded in
    (* Transitive overlap components. *)
    let rec components acc = function
      | [] -> acc
      | (dtid, kind, ws) :: rest ->
          let overlapping, non_overlapping =
            Base.List.partition_tf acc ~f:(fun comp ->
                Base.List.exists comp ~f:(fun (_, _, ws') -> WordSet.overlap ws ws'))
          in
          let new_comp =
            (dtid, kind, ws) :: Base.List.concat overlapping
          in
          components (new_comp :: non_overlapping) rest
    in
    let init_map =
      Base.List.fold unbounded_or_dead ~init:Tid.Map.empty ~f:(fun acc (dtid, kind, _) ->
          Core.Map.set acc ~key:dtid ~data:kind)
    in
    Base.List.fold_left (components [] items) ~init:init_map
      ~f:(fun acc comp ->
        match comp with
        | [ (dtid, kind, _) ] -> Core.Map.set acc ~key:dtid ~data:kind
        | _ ->
            let lo, hi =
              match comp with
              | (_, k0, _) :: rest ->
                let slo0, shi0 = span_of k0 in
                Base.List.fold_left rest ~init:(slo0, shi0)
                  ~f:(fun (l, h) (_, k, _) ->
                    let slo, shi = span_of k in
                    (Stdlib.Int64.min l slo, Stdlib.Int64.max h shi))
              | [] -> (0L, 0L) (* Non-empty components. *)
            in
            Base.List.fold_left comp ~init:acc
              ~f:(fun acc (dtid, _, _) ->
                  Core.Map.set acc ~key:dtid ~data:(Range (lo, hi))))
  in
  (* The producer's lane split: positives are the ABI-visible caller
     window (the hike_stack lane); negatives and mixed spans are this
     sub's frame (the uniform frame rule). *)
  let offsets =
      Base.List.fold raw ~init:Tid.Map.empty ~f:(fun m (dtid, kind, _) ->
          let k = match Core.Map.find merged_tags dtid with
            | Some k -> k
            | None -> kind in
          Core.Map.set m ~key:dtid ~data:(caller_split k)) in
  (* vla_bounds is DELETED (the no-gates ruling): its only production
     readers were the VLA-overlap gates.  Dynamic allocation itself travels
     in [vla_alloc_tids] (the runtime-alloca rule's input). *)
  offsets

(* True for [RSP := RSP - size]. *)
and vla_decrement_p (sp_base : var) (rhs : Bil.exp) : bool =
  match rhs with
  | Bil.BinOp (Bil.MINUS, Bil.Var a, size) ->
      Var.same (Var.base a) sp_base
      && (match size with Bil.Int _ -> false | _ -> true)
  | _ -> false

(* Runtime-sized SP decrements — relocated unchanged from the deleted
   relevance pass (spec §2.3); the hike-vsa pass calls it once per sub. *)
and detect_dynamic_alloc (sp : var) (sub : sub term) : Tid.Set.t =
  let sp_base = Var.base sp in
  let def_of_lhs =
    Term.enum blk_t sub
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.fold ~init:Var.Map.empty ~f:(fun m d ->
        Core.Map.set m ~key:(Var.base (Def.lhs d)) ~data:d)
  in
  let is_sp_var (v : var) : bool = Var.same (Var.base v) sp_base in
  let find_def (v : var) : def term option = Core.Map.find def_of_lhs (Var.base v) in
  let is_dynamic_sp_decrement (e : exp) : bool =
    vla_decrement_p sp_base e
  in
  let v =
    object
      inherit [Tid.Set.t] Term.visitor
      method! visit_def d acc =
        let lhs = Def.lhs d in
        if is_sp_var lhs then
          let rhs = Def.rhs d in
          if is_dynamic_sp_decrement rhs then
            Core.Set.add acc (Term.tid d)
          else
            match rhs with
            | Bil.Var tmp ->
                (match find_def tmp with
                 | Some d' when is_dynamic_sp_decrement (Def.rhs d') ->
                     Core.Set.add (Core.Set.add acc (Term.tid d)) (Term.tid d')
                 | _ -> acc)
            | _ -> acc
        else acc
    end
  in
  v#visit_sub sub Tid.Set.empty

end

(* Re-exports for the mli's fixture seam (the F1 family constructs these). *)
type refine_ctx = Cbat_runctx.refine_ctx
let mk_rctx = Cbat_runctx.mk_rctx
let walk_budget (rc : refine_ctx) : int ref = rc.Cbat_runctx.rc_walk_budget

(* The frozen seam (cbat_vsa.mli): transfer and walk live in sibling
   modules; this interface re-exports them. The driver below consumes
   both; neither consumes this module (no cycle by construction). *)

let set_addr_bits = Cbat_transfer.set_addr_bits
let denote_def = Cbat_transfer.denote_def
let denote_defs = Cbat_transfer.denote_defs
let denote_imm_exp = Cbat_transfer.denote_imm_exp
let reachable_jumps = Cbat_transfer.reachable_jumps

type analysis_ctx = Cbat_walk.analysis_ctx = {
  defs : (def term * bool) Var.Map.t option;
  stores : def term list option;
  flag_state : (var * Bil.binop * exp * word) option;
  has_sub : bool;
}

type edge_constraint = Cbat_walk.edge_constraint =
  | Var of var * WordSet.t
  | Cell of exp * exp * Size.t * endian * WordSet.t
  | Infeasible

module Live = Cbat_walk.Live

let assume_jump_cond = Cbat_walk.assume_jump_cond
let constrain_cell_on_trace = Cbat_walk.constrain_cell_on_trace
let edge_constraints = Cbat_walk.edge_constraints

let refine_edge = Cbat_walk.refine_edge

(* The fixtures' construction seam (cbat_vsa.mli's Test_seam). *)
module Test_seam = struct
  type refine_ctx = Cbat_runctx.refine_ctx
  type analysis_ctx = Cbat_walk.analysis_ctx = {
    defs : (def term * bool) Var.Map.t option;
    stores : def term list option;
    flag_state : (var * Bil.binop * exp * word) option;
    has_sub : bool;
  }
  type edge_constraint = Cbat_walk.edge_constraint =
    | Var of var * WordSet.t
    | Cell of exp * exp * Size.t * endian * WordSet.t
    | Infeasible
  module Live = Live
  let denote_def = denote_def
  let denote_defs = denote_defs
  let denote_imm_exp = denote_imm_exp
  let reachable_jumps = reachable_jumps
  let assume_jump_cond = assume_jump_cond
  let constrain_cell_on_trace = constrain_cell_on_trace
  let edge_constraints = edge_constraints
  let mk_rctx = mk_rctx
  let walk_budget = walk_budget
  let refine_edge = refine_edge
  let defs_of_sub = defs_of_sub
end
