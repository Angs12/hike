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

(* The dispatch guard construction shared with the Hike worklist. *)
module Dispatch = Cbat_dispatch
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

(* WTO over the engine's current block set; [succ]/[pred] are the
   dispatch graph's accessors — the resolved dispatches' extra edges ride
   BOTH, so the ordering closes on the same graph pair it walks. *)
let wto_of_cfg ~(succ : tid -> tid list) ~(pred : tid -> tid list)
    ~(nodes : tid list) : Cbat_wto.comp list =
  Cbat_wto.wto ~nodes ~succ ~pred


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

let reset_memos () = Cbat_clp_set_scalar.reset_memos ()

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

(* [run_state] is the canonical context, not a wrapper around one. *)
type run_state = Cbat_runctx.refine_ctx

(* A site materialization request.  The callback owns target enumeration,
   validation and any lifting/solving; VSA owns installing the returned
   transfer in the source block and delivering its edges in the current
   fan-out.  [None] leaves the indirect transfer untouched. *)
type materialize_transfer =
  state:run_state ->
  source:Tid.t ->
  blk:blk term ->
  jmp:jmp term ->
  env:AI.t ->
  Dispatch.materialized option

let no_materialize_transfer : materialize_transfer =
  fun ~state:_ ~source:_ ~blk:_ ~jmp:_ ~env:_ -> None

let sol_map_of_sol (sol : vsa_sol) : AI.t Tid.Map.t =
  Solution.enum sol
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun m (k, v) ->
      Core.Map.set m ~key:k ~data:v)

let state_sol (st : run_state) : vsa_sol =
  Solution.create st.rs_store st.rs_default

(* The canonical context: [run_state] is this value, not a wrapper. *)
let state_ctx (st : run_state) : Cbat_runctx.refine_ctx = st

let state_current (st : run_state) : Tid.t option = st.rs_current
let state_pending (st : run_state) : Tid.Set.t = st.rs_pending
let state_sub (st : run_state) : Sub.t = st.rs_sub
let state_resolved (st : run_state) : Tid.Set.t Tid.Map.t = st.rs_resolved
let state_synth (st : run_state) : Hike_synth.table =
  !(st.rc_synth)

(* The widening heads and each block's innermost head, saved with the
   state.  Exposed for growth pins and the WTO evidence. *)
let state_heads (st : run_state) : Tid.Set.t = st.rs_heads
let state_head_of (st : run_state) (v : Tid.t) : Tid.t option =
  Hashtbl.find st.rs_block_to_head v

(* Replace the solution/store for an external restart, keeping the whole
   [refine_ctx] (block facts, delivered edges, landmarks, synth and
   lookup), the incoming joins and the visit counters.  A restart has no
   saved cursor, and woken sources are refreshed explicitly. *)
let state_with_sol (st : run_state) (sol : vsa_sol) : run_state =
  { st with
    rs_store = sol_map_of_sol sol;
    rs_default = Solution.default sol;
    rs_pending = Tid.Set.empty;
    rs_unplaced = Tid.Set.empty;
    rs_current = None;
    rs_reseed = Tid.Set.empty;
    rs_fan = Tid.Set.empty;
    rs_heads = st.rs_heads;
    rs_block_to_head = st.rs_block_to_head }

(* Add or replace the facts of a sub a site install changed.  This is the
   only way [rc_blocks] grows after construction; [mk_rctx] is never
   called again, and an unchanged block keeps its existing facts. *)
let state_with_sub (st : run_state) (s : Sub.t) : run_state =
  let abi = st.rc_abi in
  Term.enum blk_t s
  |> Seq.iter ~f:(fun b ->
      let tid = Term.tid b in
      match Core.Map.find st.rc_blocks tid with
      | Some bf when phys_equal bf.Cbat_runctx.bf_term b -> ()
      | _ ->
        st.rc_blocks <-
          Core.Map.set st.rc_blocks ~key:tid
            ~data:(Cbat_runctx.block_facts_of_block ~abi b));
  st.rc_preserved <- Cbat_runctx.preserved_of_sub ~abi s;
  st.rc_edge_conds <- Cbat_runctx.edge_conds_of s;
  st.rc_disabled_conds <-
    Cbat_runctx.disabled_conds_of ~edge_conds:st.rc_edge_conds s;
  (* The graph, ordering and plans are functions of the old sub; the new
     sub invalidates them.  The solve rebuilds them once, not per resume. *)
  { st with rs_sub = s;
    rs_dg = None;
    rs_wto = None;
    rs_smry = None;
    rs_need = None;
    rs_max_steps = None;
    rs_plan = None;
    rs_heads = Tid.Set.empty;
    rs_block_to_head = Hashtbl.create (module Tid) }

(* Install a newer synth table in the same context cell; no block facts
   or plans are rebuilt. *)
let state_with_synth (st : run_state) (synth : Hike_synth.table) : run_state =
  st.rc_synth := synth;
  st

let static_graph_vsa
    ~(abi : Hike_abi.t)
    ~def_reads ~def_writes ~phi_reads ~phi_writes ~jmp_reads
    ?(callee : Tid.t -> Cbat_call_effects.callee =
        fun _ -> Cbat_call_effects.Summary None)
    ?(resolved : Tid.Set.t Tid.Map.t = Tid.Map.empty)
    ?(sub_lookup : int64 -> Tid.t option = fun _ -> None)
    ?(wake : Tid.Set.t = Tid.Set.empty)
    ?state
    ?(materialize_transfer : materialize_transfer = no_materialize_transfer)
    ~(synth : Hike_synth.table ref)
    (s_arg : Sub.t) (init : vsa_sol) : vsa_sol * run_state =
  (* A true entry that is also a loop header has a start-pseudo phi
     operand for its initial value.  Bind that operand from the entry
     seed once, so the first iteration starts from the seed rather than
     from the backedge alone. *)
  let init =
    match entry_block_of s_arg with
    | Some entry
      when Term.enum phi_t entry |> Seq.exists ~f:(fun p ->
               Seq.exists (Phi.values p) ~f:(fun (src, _) ->
                   Tid.equal src Graphs.Tid.start)) ->
      let tid = Term.tid entry in
      let state = Solution.get init tid in
      let state =
        Cbat_transfer.denote_phis ~synth:!synth ~source:Graphs.Tid.start
          entry state
      in
      Solution.create
        (Core.Map.set (sol_map_of_sol init) ~key:tid ~data:state)
        (Solution.default init)
    | _ -> init
  in
  let fresh = Option.is_none state in
  let st =
    match state with
    | Some st -> st
    | None ->
      let s = normalize_round_with_synth ~synth s_arg in
      let ctx =
        mk_rctx_with_oracle ~abi ~def_reads ~def_writes ~phi_writes
          ~jmp_reads ~synth ~sub_lookup s in
      { ctx with
        rs_sub = s;
        rs_store = sol_map_of_sol init;
        rs_default = Solution.default init;
        rs_incoming = Tid.Map.empty;
        rs_pending = Tid.Set.empty;
        rs_unplaced = Tid.Set.empty;
        rs_total_processed = 0;
        rs_head_visits = Hashtbl.create (module Tid);
        rs_current = None;
        rs_resolved = resolved;
        rs_reseed = Tid.Set.empty;
        rs_fan = Tid.Set.empty;
        rs_heads = Tid.Set.empty;
        rs_block_to_head = Hashtbl.create (module Tid);
        rs_dg = None;
        rs_wto = None;
        rs_smry = None;
        rs_need = None;
        rs_max_steps = None;
        rs_plan = None }
  in
  let s = st.rs_sub in
  let rctx = st in
  (* The persisted rctx owns the synth ref; an external restart may carry
     a newer table value, so refresh the cell without rebuilding. *)
  rctx.Cbat_runctx.rc_synth := !synth;
  (* The active resolution view: persisted on save, and the source of
     every plan's edge relation. *)
  let resolved_ref = ref resolved in
  let saved_sub = ref s in
  let preserved = ref st.rc_preserved in
  let edge_conds = ref st.rc_edge_conds in
  let disabled_conds = ref st.rc_disabled_conds in
  (* Reuse the persisted graph/order/plan caches only for a paused resume
     with the same static inputs.  A changed sub or resolution view
     invalidates them in [state_with_sub]. *)
  let resume_meta =
    match state with
    | Some st when
        Core.Map.equal (fun a b -> Tid.Set.equal a b)
          st.rs_resolved resolved ->
      Some st
    | _ -> None
  in
  (* Plans are the one derived cache the solver owns: a site install
     invalidates only the affected source, and the next lookup rebuilds
     against the current blocks/edge conditions/resolution.  A resumed
     solve reuses the persisted closure until it changes. *)
  let compute_plan (source : Tid.t) : Cbat_runctx.block_plan =
    Cbat_forward.plan_block ~resolved:!resolved_ref ~edge_conds:!edge_conds
      ~disabled:!disabled_conds ~rctx source
  in
  let plan_table : Cbat_runctx.block_plan Tid.Table.t = Tid.Table.create () in
  let resumed_plan =
    ref (match resume_meta with Some st -> st.rs_plan | None -> None) in
  let plan_of source =
    match Hashtbl.find plan_table source with
    | Some p -> p
    | None ->
      let p = match !resumed_plan with
        | Some f -> f source
        | None -> compute_plan source in
      Hashtbl.set plan_table ~key:source ~data:p;
      p
  in
  let set_plan source p = Hashtbl.set plan_table ~key:source ~data:p in
  let rebuild_plan source = set_plan source (compute_plan source) in
  (* Pseudo-nodes never reach denotation. *)
  let cfg_of_sub (sub : Sub.t) =
    Sub.to_graph sub
    |> Graphs.Tid.Node.remove Graphs.Tid.start
    |> Graphs.Tid.Node.remove Graphs.Tid.exit
  in
  let tids_of_sub (sub : Sub.t) : Tid.t list =
    Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Seq.to_list
  in
  let block_set (sub : Sub.t) : Tid.Set.t =
    Tid.Set.of_list (tids_of_sub sub) in
  (* The dispatch graph: the CFG plus the Resolved dispatches' extra
     edges, serving the WTO, the worklist, and the predecessor lists.  It
     is rebuilt from the current sub/resolution after a growth delta, so
     both new vertices and retired edges reach the ordering. *)
  let make_dg () =
    Cbat_dispatch_graph.make ~cfg:(cfg_of_sub s) ~blocks:(block_set s)
      !resolved_ref s in
  let dg_ref =
    ref (match resume_meta with
         | Some st ->
           (match st.rs_dg with Some dg -> dg | None -> make_dg ())
         | None -> make_dg ()) in
  let succs (v : Tid.t) : Tid.t list = (!dg_ref).Cbat_dispatch_graph.succs v in
  let preds (v : Tid.t) : Tid.t list = (!dg_ref).Cbat_dispatch_graph.preds v in
  (* WTO fixpoint; inner SCCs stabilize first.  A paused resume installs
     the saved ordering and summary; growth refreshes them. *)
  let make_wto () =
    wto_of_cfg ~succ:succs ~pred:preds ~nodes:(tids_of_sub s) in
  let wto_ref =
    ref (match resume_meta with
         | Some st ->
           (match st.rs_wto with Some w -> w | None -> make_wto ())
         | None -> make_wto ()) in
  let smry_ref =
    ref (match resume_meta with
         | Some st ->
           (match st.rs_smry with
            | Some sm -> sm
            | None -> Cbat_wto.summary !wto_ref)
         | None -> Cbat_wto.summary !wto_ref) in
  let heads_ref = ref (!smry_ref).Cbat_wto.heads in
  let head_to_blocks_ref = ref (!smry_ref).Cbat_wto.head_to_blocks in
  let block_to_head_ref = ref (!smry_ref).Cbat_wto.block_to_head in
  let build_need ~(head_to_blocks : (Tid.t, Tid.Set.t) Hashtbl.t) :
      Core.Int.Set.t Tid.Map.t =
    Hashtbl.fold head_to_blocks ~init:Tid.Map.empty
      ~f:(fun ~key:h ~data:blocks acc ->
        Core.Map.set acc ~key:h
          ~data:(Cbat_var_id.intern_set
                   (compute_need ~def_reads ~phi_reads
                      ~rc_blocks:rctx.rc_blocks blocks)))
  in
  let need_map_ref =
    ref (match resume_meta with
         | Some st ->
           (match st.rs_smry, st.rs_need with
            | Some _, Some need -> need
            | _ -> build_need ~head_to_blocks:!head_to_blocks_ref)
         | None -> build_need ~head_to_blocks:!head_to_blocks_ref) in
  let sol_default = st.rs_default in
  (* The solve's own store: each block's state is what the block needs —
     the values it receives and the memory it carries.  The values a
     block computes are a derived working set, never stored here. *)
  let sol_store = ref st.rs_store in
  let get n = Option.value (Core.Map.find !sol_store n) ~default:sol_default in
  let set n v = sol_store := Core.Map.set !sol_store ~key:n ~data:v in
  let mk_sol () = Solution.create !sol_store sol_default in
  Stages.reset ();
  let total_processed = ref st.rs_total_processed in
  let max_steps =
    ref (match resume_meta with
         | Some st ->
           (match st.rs_max_steps with
            | Some n -> n
            | None -> visit_budget !wto_ref)
         | None -> visit_budget !wto_ref) in
  (* Per-head visit counts; each head gets its own warmup window. *)
  let head_visits = st.rs_head_visits in
  let head_warmed (v : Tid.t) : bool =
    Option.value ~default:0 (Hashtbl.find head_visits v)
    > head_warmup_visits in
  (* The solver is source-oriented: a source IN state is replayed once,
     then its edge states fan out to every successor; [incoming_store]
     keeps the join of the edge states delivered so far for each target.
     Both this join and [rctx.rc_edges] are part of the persisted state. *)
#ifdef VSA_DEBUG
  let head_arm = ref "" in
  let dbg_fan_calls = ref 0 in
#endif
  let delivered_at ~(source : Tid.t) ~(target : Tid.t) : AI.t =
    match Core.Map.find !(rctx.Cbat_runctx.rc_edges) source with
    | None -> AI.bottom
    | Some edges -> Option.value (Core.Map.find edges target) ~default:AI.bottom
  in
  let incoming_store = ref st.rs_incoming in
  (* The target's joined incoming state over the tracked edge
     contributions.  Unchanged warm-seed contributions are already
     joined into the target's state, so they need not be re-delivered. *)
  let recompute_incoming (v : Tid.t) : AI.t =
    List.fold (preds v) ~init:AI.bottom
      ~f:(fun acc p -> AI.join acc (delivered_at ~source:p ~target:v))
  in
  (* Succ-seeded WTO-priority worklist; every visit runs process_vertex
     completely, and changed sources enqueue their targets.  The queue
     pops the lowest WTO position, whose block is unique: [pending] holds
     one block per position, and [unplaced] the blocks outside the WTO,
     which pop last in Tid order. *)
  let pending : Tid.t Int.Map.t ref = ref Int.Map.empty in
  let unplaced = ref st.rs_unplaced in
  let enqueue t =
    match Core.Map.find (!smry_ref).Cbat_wto.pos_of t with
    | Some p -> pending := Core.Map.set !pending ~key:p ~data:t
    | None -> unplaced := Core.Set.add !unplaced t
  in
  Core.Set.iter st.rs_pending ~f:enqueue;
  let current = ref st.rs_current in
  (* Deferred seed work survives an in-place install. *)
  let reseed_pending = ref st.rs_reseed in
  let fan_pending = ref st.rs_fan in
  (* Rebuild the dispatch graph from the current sub/resolution.  Called
     after a growth delta: new vertices and retired edges reach the
     ordering and the predecessor lists in one place. *)
  let rebuild_graph () =
    let sub = !saved_sub in
    dg_ref :=
      Cbat_dispatch_graph.make ~cfg:(cfg_of_sub sub) ~blocks:(block_set sub)
        !resolved_ref sub
  in
  (* Refresh the WTO/head/need/position metadata from the updated graph.
     The solution, incoming joins, landmarks, visit counters, every
     pending entry and the saved cursor are preserved; only positions are
     recomputed, so the pending set is re-inserted by the new priority. *)
  let rebuild_wto () =
    let wto = wto_of_cfg ~succ:succs ~pred:preds
        ~nodes:(tids_of_sub !saved_sub) in
    wto_ref := wto;
    let smry = Cbat_wto.summary wto in
    smry_ref := smry;
    heads_ref := smry.Cbat_wto.heads;
    head_to_blocks_ref := smry.Cbat_wto.head_to_blocks;
    block_to_head_ref := smry.Cbat_wto.block_to_head;
    need_map_ref := build_need ~head_to_blocks:smry.Cbat_wto.head_to_blocks;
    (* Growth extends the allowance for the new vertices; a paused
       resume must not reset the budget it already spent. *)
    max_steps := Stdlib.max !max_steps (visit_budget wto);
    let keep =
      Core.Map.fold !pending ~init:!unplaced
        ~f:(fun ~key:_ ~data:t acc -> Core.Set.add acc t)
    in
    pending := Int.Map.empty;
    unplaced := Tid.Set.empty;
    Core.Set.iter keep ~f:enqueue
  in
  (* Record one delivered edge state and enqueue the target when its
     joined incoming state changes.  A monotone edge update replaces its
     old contribution by the new one; a non-monotone update (a resolution
     can retire an edge) recomputes the target's join. *)
  let note_edge ~(source : Tid.t) ~(target : Tid.t)
      ~(old_delivered : AI.t) (delivered : AI.t) : unit =
    let edges =
      Option.value (Core.Map.find !(rctx.Cbat_runctx.rc_edges) source)
        ~default:Tid.Map.empty in
    rctx.Cbat_runctx.rc_edges :=
      Core.Map.set !(rctx.Cbat_runctx.rc_edges) ~key:source
        ~data:(Core.Map.set edges ~key:target ~data:delivered);
    if not (AI.equal old_delivered delivered) then begin
      let previous =
        Option.value (Core.Map.find !incoming_store target)
          ~default:AI.bottom in
      let incoming =
        if AI.equal old_delivered AI.bottom
           || AI.precedes old_delivered delivered
        then AI.join previous delivered
        else recompute_incoming target
      in
      let changed = not (AI.equal previous incoming) in
      incoming_store :=
        Core.Map.set !incoming_store ~key:target ~data:incoming;
      (* A contribution already covered by the target's warm state changes
         no state; processing it would only replay work. *)
      if changed && not (AI.precedes incoming (get target)) then
        enqueue target
    end
  in
  (* The transfers a site materializer may own: an indirect Goto, or an
     indirect Call (a normal call or a noreturn tail call). *)
  let materializable_target (j : jmp term) : exp option =
    match Jmp.kind j with
    | Goto (Indirect e) -> Some e
    | Call c -> (
        match Call.target c with
        | Indirect e -> Some e
        | Direct _ -> None)
    | _ -> None
  in
  let is_true_cond (e : exp) : bool =
    match e with
    | Bil.Int w -> Word.equal w (Word.one 1)
    | _ -> false
  in
  (* The source block's term-order follower: the conditional fallthrough
     edge the completion pass materializes from the same order. *)
  let term_follower (sub : Sub.t) (source : Tid.t) : Tid.t option =
    let rec find = function
      | a :: (b :: _ as rest) ->
        if Tid.equal a source then Some b else find rest
      | _ -> None
    in
    find (Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Seq.to_list)
  in
  (* The installed chain is not an ordinary conditional jmp: every piece
     is a conditional Goto, and the last one needs its explicit false
     edge before the splitter runs.  The source's term-order follower is
     that continuation; an already explicit one is left alone. *)
  let complete_false_edge ~(source : Tid.t) (blk : blk term) : blk term =
    match Base.List.last (Term.enum jmp_t blk |> Seq.to_list) with
    | Some j
      when (match Jmp.kind j with Goto (Direct _) -> true | _ -> false)
           && not (is_true_cond (Jmp.cond j)) -> (
        match term_follower !saved_sub source with
        | Some follower ->
          Term.append jmp_t blk (Jmp.create (Goto (Direct follower)))
        | None -> blk)
    | _ -> blk
  in
  let has_block (s : Sub.t) tid = Option.is_some (Term.find blk_t s tid) in
  let source_block source =
    match Term.find blk_t !saved_sub source with
    | Some b -> b
    | None ->
      (Core.Map.find_exn rctx.Cbat_runctx.rc_blocks source).bf_term
  in
  (* The callback may already have rewritten the source and run its SSA
     (the production worklist path).  Then the install only refreshes the
     context and recomputes the source post-state; the BIR construction
     below is the fallback for a synthetic callback that leaves the source
     jmp unchanged. *)
  let install_materialization ~(source : Tid.t) ~(blk : blk term)
      ~(jmp : jmp term) ~(entry : AI.t) ~(forward : AI.t)
      (m : Dispatch.materialized) : AI.t =
    let jmp_tids b = Term.enum jmp_t b |> Seq.map ~f:Term.tid |> Seq.to_list in
    let rewritten =
      match Term.find blk_t m.Dispatch.sub source with
      | Some b -> not (Base.List.equal Tid.equal (jmp_tids b) (jmp_tids blk))
      | None -> false
    in
    if rewritten then begin
      let sub = m.Dispatch.sub in
      saved_sub := sub;
      preserved := Cbat_runctx.preserved_of_sub ~abi sub;
      edge_conds := Cbat_runctx.edge_conds_of sub;
      disabled_conds :=
        Cbat_runctx.disabled_conds_of ~edge_conds:!edge_conds sub;
      rctx.Cbat_runctx.rc_preserved <- !preserved;
      rctx.Cbat_runctx.rc_edge_conds <- !edge_conds;
      rctx.Cbat_runctx.rc_disabled_conds <- !disabled_conds;
      (* The rewritten source, its new blocks and every old target whose
         phis changed all carry new terms; only an unchanged block keeps
         its previous facts. *)
      Term.enum blk_t sub
      |> Seq.iter ~f:(fun b ->
             let tid = Term.tid b in
             match Core.Map.find rctx.Cbat_runctx.rc_blocks tid with
             | Some bf when phys_equal bf.Cbat_runctx.bf_term b -> ()
             | Some _ ->
               rctx.Cbat_runctx.rc_blocks <-
                 Core.Map.set rctx.Cbat_runctx.rc_blocks ~key:tid
                   ~data:(Cbat_runctx.block_facts_of_block ~abi b)
             | None ->
               sol_store :=
                 Core.Map.set !sol_store ~key:tid ~data:AI.bottom;
               incoming_store :=
                 Core.Map.set !incoming_store ~key:tid ~data:AI.bottom;
               rctx.Cbat_runctx.rc_blocks <-
                 Core.Map.set rctx.Cbat_runctx.rc_blocks ~key:tid
                   ~data:(Cbat_runctx.block_facts_of_block ~abi b));
      rebuild_plan source;
      Cbat_forward.denote_block ~rctx (plan_of source) ~entry
    end else begin
    let target = Option.value_exn (materializable_target jmp) in
    let original =
      match Jmp.kind jmp with
      | Call c when Option.is_some (Call.return c) -> Some c
      | _ -> None
    in
    let kind = if Option.is_some original then Dispatch.Call else Dispatch.Jump in
    let binding, arms =
      Dispatch.materialize m ~kind ~cond:(Some (Jmp.cond jmp)) ~target
    in
    (* An unconditional indirect jump has no false continuation: its
       complete target set is exhaustive, so the last arm is the default
       terminator. *)
    let arms =
      if Option.is_none original
         && is_true_cond (Jmp.cond jmp)
         && not (List.is_empty arms)
      then
        List.mapi arms ~f:(fun i a ->
            if i + 1 = List.length arms then
              { a with Dispatch.guard = Bil.Int (Word.one 1) }
            else a)
      else arms
    in
    (* The callback may have bound the base summand in the source block.
       Keep its defs/phis, our current jmps (including an earlier install
       in this same fan-out), and any fresh defs of ours. *)
    let blk =
      match Term.find blk_t m.sub source with
      | None -> blk
      | Some mb when phys_equal mb blk -> blk
      | Some mb ->
        let b =
          Blk.Builder.init ~copy_defs:true ~copy_phis:true ~copy_jmps:false
            mb
        in
        Term.enum def_t blk
        |> Seq.iter ~f:(fun d ->
               if Option.is_none (Term.find def_t mb (Term.tid d)) then
                 Blk.Builder.add_def b d);
        Term.enum phi_t blk
        |> Seq.iter ~f:(fun p ->
               if Option.is_none (Term.find phi_t mb (Term.tid p)) then
                 Blk.Builder.add_phi b p);
        Term.enum jmp_t blk |> Seq.iter ~f:(Blk.Builder.add_jmp b);
        Blk.Builder.result b
    in
    let trap =
      match original with
      | None -> None
      | Some _ ->
        (* A normal block whose one jmp is [Int]: the emitter already
           renders it as a trap, so it needs no special name. *)
        let tid = Tid.create () in
        Some (tid, Some (Blk.create ~tid ~jmps:[ Jmp.create_int 0 tid ] ()))
    in
    let is_intra tid = has_block m.sub tid || has_block !saved_sub tid in
    let return = match original with Some c -> Call.return c | None -> None in
    let arms =
      match trap with
      | None ->
        List.map arms ~f:(Dispatch.arm_jmp ~kind ~return ~is_intra)
      | Some (trap_tid, _) ->
        let cond = Jmp.cond jmp in
        let trap_jmp =
          if is_true_cond cond then Jmp.create (Goto (Direct trap_tid))
          else Jmp.create ~cond (Goto (Direct trap_tid))
        in
        List.map arms ~f:(Dispatch.arm_jmp ~kind ~return ~is_intra)
        @ [ trap_jmp ]
    in
    let blk =
      if List.is_empty arms then blk
      else
        Term.concat_map jmp_t blk ~f:(fun j ->
            if Tid.equal (Term.tid j) (Term.tid jmp) then arms else [ j ])
    in
    (* Only a conditional original has a false continuation.  An
       unconditional indirect jump's target set is exhaustive. *)
    let blk =
      if is_true_cond (Jmp.cond jmp) then blk
      else complete_false_edge ~source blk
    in
    let blk, forward =
      match binding with
      | None -> (blk, forward)
      | Some (v, d) ->
        let blk = Term.append def_t blk d in
        let forward =
          match
            Cbat_transfer.denote_imm_exp
              ~synth:!(rctx.Cbat_runctx.rc_synth) (Def.rhs d) forward
          with
          | Ok ws -> AI.add_word forward ~key:v ~data:ws
          | Error _ -> forward
        in
        (blk, forward)
    in
    (* The callback's m.sub carries new blocks; keep the old sub's term
       order (the completion's fallthrough edge reads it) and append only
       blocks the SSA view introduced. *)
    let sub =
      Term.enum blk_t !saved_sub
      |> Seq.fold ~init:m.sub ~f:(fun s b ->
             if Option.is_some (Term.find blk_t s (Term.tid b)) then s
             else Term.append blk_t s b)
    in
    let sub =
      match Term.find blk_t sub source with
      | Some _ -> Term.update blk_t sub blk
      | None -> Term.append blk_t sub blk
    in
    let sub =
      match trap with
      | Some (_, Some b) -> Term.append blk_t sub b
      | Some (_, None) | None -> sub
    in
    saved_sub := sub;
    preserved := Cbat_runctx.preserved_of_sub ~abi sub;
    edge_conds := Cbat_runctx.edge_conds_of sub;
    disabled_conds :=
      Cbat_runctx.disabled_conds_of ~edge_conds:!edge_conds sub;
    rctx.Cbat_runctx.rc_preserved <- !preserved;
    rctx.Cbat_runctx.rc_edge_conds <- !edge_conds;
    rctx.Cbat_runctx.rc_disabled_conds <- !disabled_conds;
    rctx.Cbat_runctx.rc_blocks <-
      Core.Map.set rctx.Cbat_runctx.rc_blocks ~key:source
        ~data:(Cbat_runctx.block_facts_of_block ~abi blk);
    Term.enum blk_t sub
    |> Seq.iter ~f:(fun b ->
           let tid = Term.tid b in
           if not (Core.Map.mem rctx.Cbat_runctx.rc_blocks tid) then begin
             (* First sight of a block: its pre-state is bottom, so the
                current fan-out's delivery is its first incoming state. *)
             sol_store := Core.Map.set !sol_store ~key:tid ~data:AI.bottom;
             incoming_store :=
               Core.Map.set !incoming_store ~key:tid ~data:AI.bottom;
             rctx.Cbat_runctx.rc_blocks <-
               Core.Map.set rctx.Cbat_runctx.rc_blocks ~key:tid
                 ~data:(Cbat_runctx.block_facts_of_block ~abi b)
           end);
    (* Only the source's plan changed; the graph and ordering refresh
       once after the source's installs. *)
    rebuild_plan source;
    forward
    end
  in
  let save_state () : run_state =
    let pending_tids =
      Core.Map.fold !pending ~init:Tid.Set.empty
        ~f:(fun ~key:_ ~data:v acc -> Core.Set.add acc v) in
    { st with
      rc_preserved = !preserved;
      rc_edge_conds = !edge_conds;
      rc_disabled_conds = !disabled_conds;
      rs_sub = !saved_sub;
      rs_store = !sol_store;
      rs_default = sol_default;
      rs_incoming = !incoming_store;
      rs_pending = pending_tids;
      rs_unplaced = !unplaced;
      rs_total_processed = !total_processed;
      rs_head_visits = head_visits;
      rs_current = !current;
      rs_resolved = !resolved_ref;
      rs_reseed = !reseed_pending;
      rs_fan = !fan_pending;
      rs_heads = !heads_ref;
      rs_block_to_head = !block_to_head_ref;
      rs_dg = Some !dg_ref;
      rs_wto = Some !wto_ref;
      rs_smry = Some !smry_ref;
      rs_need = Some !need_map_ref;
      rs_max_steps = Some !max_steps;
      rs_plan = Some plan_of }
  in
  (* One source IN state: replay its definitions once, install any site
     materializations, then deliver every outgoing edge with its own
     backward refinement.  An install's new case edges are delivered by
     this same fan-out; the source is never re-enqueued. *)
  let fan_out (source : Tid.t) (state : AI.t) : unit =
#ifdef VSA_DEBUG
    incr dbg_fan_calls;
#endif
    current := Some source;
    let dedup_targets () =
      List.fold (succs source) ~init:[] ~f:(fun acc t ->
          if Base.List.mem acc t ~equal:Tid.equal then acc else t :: acc)
      |> List.rev
    in
    let candidates =
      if phys_equal materialize_transfer no_materialize_transfer then []
      else
        Term.enum jmp_t (source_block source)
        |> Seq.filter ~f:(fun j ->
               Option.is_some (materializable_target j))
        |> Seq.to_list
    in
    if not
         (List.is_empty (dedup_targets ())
         && List.is_empty candidates)
    then begin
      let plan = plan_of source in
      let forward = Stages.time `Denote (fun () ->
          Cbat_forward.denote_block ~rctx plan ~entry:state) in
      let installed = ref false in
      let forward =
        List.fold candidates ~init:forward ~f:(fun forward jmp ->
            let blk = source_block source in
            match
              materialize_transfer ~state:(save_state ()) ~source ~blk ~jmp
                ~env:forward
            with
            | None -> forward
            | Some m ->
              installed := true;
              install_materialization ~source ~blk ~jmp ~entry:state ~forward m)
      in
      if !installed then begin
        rebuild_graph ();
        rebuild_wto ()
      end;
      let plan = plan_of source in
      List.iter (dedup_targets ()) ~f:(fun target ->
          let old_delivered = delivered_at ~source ~target in
          let res =
            if AI.equal forward AI.bottom then AI.bottom
            else
              Cbat_landmarks.with_widening_head
                rctx.Cbat_runctx.rc_landmarks
                (Hashtbl.find !block_to_head_ref source) (fun () ->
                  Stages.time `Denote (fun () ->
                      Cbat_forward.denote_jump ~preserved:!preserved
                        ~callee ~rctx plan ~source ~entry:state ~forward
                        ~target))
          in
#ifdef VSA_DEBUG
          debug_edge_result ~rctx ~edge_conds:!edge_conds ~get
            ~p:source ~v:target res;
#endif
          note_edge ~source ~target ~old_delivered res)
    end;
    current := None
  in
  (* Drop one source's delivered edges (a woken source's term changed) and
     rebuild the affected targets' joins from the remaining edges. *)
  let forget_source (source : Tid.t) : unit =
    match Core.Map.find !(rctx.Cbat_runctx.rc_edges) source with
    | None -> ()
    | Some edges ->
      rctx.Cbat_runctx.rc_edges :=
        Core.Map.remove !(rctx.Cbat_runctx.rc_edges) source;
      Core.Map.iteri edges ~f:(fun ~key:target ~data:_ ->
          let joined = recompute_incoming target in
          incoming_store :=
            Core.Map.set !incoming_store ~key:target ~data:joined)
  in
  (* A changed old target retires every edge into it; the caller then
     re-fans every predecessor, because the target's phi set changed and
     each operand must be re-delivered. *)
  let forget_target (target : Tid.t) : unit =
    rctx.Cbat_runctx.rc_edges :=
      Core.Map.fold !(rctx.Cbat_runctx.rc_edges) ~init:Tid.Map.empty
        ~f:(fun ~key:source ~data:edges acc ->
          let edges = Core.Map.remove edges target in
          if Core.Map.is_empty edges then acc
          else Core.Map.set acc ~key:source ~data:edges);
    incoming_store :=
      Core.Map.set !incoming_store ~key:target ~data:AI.bottom
  in
  (* Rebuild every incoming contribution of one target.  Used when a
     target's phi operands changed: every predecessor's delivery reads
     the new phi set, so all of them must replay, not only the sources
     with a new edge. *)
  let refan_into (target : Tid.t) : unit =
    List.iter (preds target) ~f:(fun source ->
        let state = get source in
        if not (AI.equal state AI.bottom) then fan_out source state);
    enqueue target
  in
  (* A warm head whose join grew widens by the landmark module's arm:
     Finite extrapolates; Zero advances and joins; Inf widens.
     Consumption is per key — each key reads its own row first, the
     head's arm is the fallback, and the clear spends only what was
     consumed. *)
  let widen_at_head (v : Tid.t) ~(old : AI.t) ~(incoming : AI.t) : AI.t =
    let need =
      Option.value ~default:Core.Int.Set.empty
        (Core.Map.find !need_map_ref v) in
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
    if Core.Set.mem !heads_ref v then begin
      let n = Option.value ~default:0 (Hashtbl.find head_visits v) in
      Hashtbl.set head_visits ~key:v ~data:(n + 1)
    end;
    if !total_processed > !max_steps then begin
      let sol = mk_sol () in
      raise (Fixpoint_not_converged (!max_steps, sol))
    end;
    let old = get v in
    let preds = preds v in
    let incoming =
      if List.is_empty preds then old
      else
        Option.value (Core.Map.find !incoming_store v) ~default:AI.bottom
    in
#ifdef VSA_DEBUG
    debug_entry ~rctx ~edge_conds:!edge_conds ~get ~preds ~v incoming;
    head_arm := "";
#endif
    let has_widened = Core.Set.mem !heads_ref v && head_warmed v in
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
      debug_churn ~head:(Core.Set.mem !heads_ref v) ~has_widened
        ~head_arm:!head_arm v old new_val;
#endif
      Stages.time `Glue (fun () -> set v new_val);
      fan_out v new_val;
      true
    end)
  in
  (* The sources a resolution delta retires or redirects.  Only these
     outgoing edges need rebuilding; the rest of the graph is unchanged. *)
  let resolved_changes ~(old : Tid.Set.t Tid.Map.t)
      ~(cur : Tid.Set.t Tid.Map.t) : Tid.Set.t =
    Term.enum blk_t !saved_sub
    |> Seq.filter ~f:(fun b ->
        Term.enum jmp_t b
        |> Seq.exists ~f:(fun j ->
            let k = Term.tid j in
            match Core.Map.find old k, Core.Map.find cur k with
            | None, None -> false
            | Some a, Some b -> not (Tid.Set.equal a b)
            | _ -> true))
    |> Seq.map ~f:Term.tid |> Seq.to_list |> Tid.Set.of_list
  in
  (* Sources whose resolved dispatch set differs from the persisted one.
     Only these are refreshed by an external restart; no global fan-out. *)
  let resolved_sources =
    if fresh then Tid.Set.empty
    else resolved_changes ~old:st.rs_resolved ~cur:!resolved_ref
  in
  (* Every source that owns a resolved dispatch.  A fresh warm start fans
     these once, because a stable warm prefix never reaches the extra
     edges on its own. *)
  let resolved_dispatch_sources =
    Term.enum blk_t s
    |> Seq.filter ~f:(fun b ->
        Term.enum jmp_t b
        |> Seq.exists ~f:(fun j -> Core.Map.mem !resolved_ref (Term.tid j)))
    |> Seq.map ~f:Term.tid |> Seq.to_list |> Tid.Set.of_list
  in
  (* Rebuild one woken block's incoming state from every predecessor and
     enqueue it.  A woken old target's phi set changed; a woken new block
     has no seed entry.  Its own outgoing edges are fanned separately. *)
  let reseed_block b =
    forget_target b;
    refan_into b
  in
  let rec reseed_deferred () =
    match Core.Set.min_elt !reseed_pending with
    | None -> ()
    | Some b ->
      reseed_block b;
      reseed_pending := Core.Set.remove !reseed_pending b;
      reseed_deferred ()
  in
  let rec fan_deferred () =
    match Core.Set.min_elt !fan_pending with
    | None -> ()
    | Some source ->
      (* A resolved view change retires the old deliveries; the replay
         below rebuilds exactly the current edge set. *)
      forget_source source;
      if not (AI.equal (get source) AI.bottom) then
        fan_out source (get source);
      fan_pending := Core.Set.remove !fan_pending source;
      fan_deferred ()
  in
  let defer_reseed tids =
    Core.Set.iter tids ~f:(fun b ->
        reseed_pending := Core.Set.add !reseed_pending b)
  in
  let defer_fan tids =
    Core.Set.iter tids ~f:(fun b ->
        fan_pending := Core.Set.add !fan_pending b)
  in
  (* Seed: a fresh start fans the entry once (and, for a warm seed, rebuilds
     the woken blocks and fans the woken/resolved sources).  An external
     restart does the same for only the woken/changed sources. *)
  let seed () =
    if fresh then
      Option.iter (entry_block_of s) ~f:(fun entry ->
          fan_out (Term.tid entry) (get (Term.tid entry)));
    let seed_sources =
      if fresh then Core.Set.union wake resolved_dispatch_sources
      else Core.Set.union wake resolved_sources
    in
    defer_reseed wake;
    defer_fan seed_sources;
    (match !current with
     | Some source when not fresh -> fan_out source (get source)
     | _ -> ());
    reseed_deferred ();
    fan_deferred ()
  in
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
      ignore (process_vertex v : bool);
      stabilize_worklist () in
  let run () = stabilize_worklist () in
  seed ();
  run ();
  Stages.report (Sub.name s);
  (mk_sol (), save_state ())

(* Re-exports for the mli's fixture seam. *)
type refine_ctx = Cbat_runctx.refine_ctx

(* The canonical run context, for the site materializer. *)
module Runctx = Cbat_runctx

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
let constrain_edge ~synth ~env ~landmarks cond =
  Cbat_backward.constrain_edge ~synth ~env ~landmarks cond

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
