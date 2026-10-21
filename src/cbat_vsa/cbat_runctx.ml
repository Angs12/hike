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


(* Per-run analysis context: static per-block facts and the versioned
   solution threaded through the engine. *)

open Core
open Bap.Std
open Graphlib.Std
module Utils = Cbat_vsa_utils
module AI = Cbat_ai_representation

(* A block's static call facts: the lanes a machine call reads and the SP
   version it reads. *)
type call_facts = {
  cf_lanes : var list;
  cf_sp : var;
}

(* The edge classification: whether a jump's transfer reaches the
   denotation target. *)
type edge_rel = Exact of Tid.Set.t | Any

type jump_plan = {
  jp_jmp : jmp term;
  jp_cond : exp option;
  jp_disabled : exp option;
  jp_rel : edge_rel;
  jp_resolved : bool;
  (* The summary's effective preserved set, keyed physically by the
     summary it was derived from. *)
  mutable jp_preserved : (Int.Set.t * Int.Set.t) option;
}

type block_plan = {
  bp_term : blk term;
  bp_call_facts : call_facts;
  bp_has_conds : bool;
  bp_jumps : jump_plan list;
}

(* Static block facts: the term, call lanes, and scalar input names. *)
type block_facts = {
  bf_term : blk term;
  bf_defs : def term list;
  (* Exact SSA lhs to its block-local statement position and definition.
     Backward scalar refinement follows this index; it does not replay
     unrelated scalar definitions. *)
  bf_def_index : (int * def term) Var.Map.t;
  bf_call_facts : call_facts;
  bf_live_ids : Int.Set.t;
}

type refine_ctx = {
  (* The run's convention facts (Hike_abi is the one home): the sp var
     the walk anchors on, the call-read lanes, and the
     word size behind every word lookup. *)
  rc_abi : Hike_abi.t;
  rc_synth : Hike_synth.table ref;
  mutable rc_blocks : block_facts Tid.Map.t;
  (* The static transfer facts derived from the sub: the preserved
     register set and the completed edge/disabled-continuation tables.
     They are part of the persisted context so a resume does not derive
     them again. *)
  mutable rc_preserved : Int.Set.t;
  mutable rc_edge_conds : exp Tid.Map.t Tid.Map.t;
  mutable rc_disabled_conds : exp Tid.Map.t;
  (* The final state each edge delivered, per (source,target): the
     values the destination receives and the memory the edge carries.
     It holds no forward post-state; the solver computes that once per
     source IN state and fans it out. *)
  rc_edges : AI.t Tid.Map.t Tid.Map.t ref;
  (* The producer non-negativity oracle (the walk's signed rows): an
     expression whose every possible value has its sign bit clear.  The
     default proves nothing. *)
  rc_nonneg : env:AI.t -> exp -> bool;
  (* The solve's own widening-landmark state (Simon & King): fresh per
     [mk_rctx], never the process's. *)
  rc_landmarks : Cbat_landmarks.t;
  (* The run's sub-address lookup: a call-target word names a lifted
     sub of this program, or none — every address foreign.  The
     indirect call site's summary derivation reads it. *)
  rc_sub_lookup : int64 -> Tid.t option;
  (* The rest of the solve's run: the static sub view, the solution
     store, the worklist/cursor, the resolution view, deferred seed work,
     and the derived graph/order/plan caches.  Keeping these here makes
     [refine_ctx] the one canonical context: a pause saves this value and
     a resume installs it as-is. *)
  rs_sub : Sub.t;
  rs_store : AI.t Tid.Map.t;
  rs_default : AI.t;
  rs_incoming : AI.t Tid.Map.t;
  rs_pending : Tid.Set.t;
  rs_unplaced : Tid.Set.t;
  rs_total_processed : int;
  rs_head_visits : (Tid.t, int) Hashtbl.t;
  (* The source whose fan-out is in progress (a completed solve leaves
     it [None]). *)
  rs_current : Tid.t option;
  rs_resolved : Tid.Set.t Tid.Map.t;
  (* Deferred seed work: woken blocks to rebuild and sources to fan once,
     finished before the main drain. *)
  rs_reseed : Tid.Set.t;
  rs_fan : Tid.Set.t;
  (* The widening metadata the solve is running with; saved so a resume
     and the growth pins see the same heads. *)
  rs_heads : Tid.Set.t;
  rs_block_to_head : (Tid.t, Tid.t) Hashtbl.t;
  (* The derived graph/order/plan caches.  A paused resume installs them
     as-is; a changed sub or resolution view clears them. *)
  rs_dg : Cbat_dispatch_graph.t option;
  rs_wto : Cbat_wto.comp list option;
  rs_smry : Cbat_wto.summary option;
  rs_need : Core.Int.Set.t Tid.Map.t option;
  rs_max_steps : int option;
  rs_plan : (Tid.t -> block_plan) option;
}

(* The block's call facts.  The program carries the SP restore of a
   call's pushed word itself. *)
let call_facts_of_block ~(abi : Hike_abi.t) (b : blk term) :
    call_facts =
  let machine_reads =
    Term.enum jmp_t b
    |> Seq.filter_map ~f:(fun j ->
           match Jmp.kind j with
           | Call _ when Hike_stack_model.machine_call j ->
             Some (Hike_stack_model.effects j).reads
           | _ -> None)
    |> Seq.concat_map ~f:Seq.of_list
    |> Seq.to_list
  in
  let is_sp v = Var.same v abi.Hike_abi.sp in
  let cf_lanes =
    List.filter machine_reads ~f:(fun v -> not (is_sp v))
    |> Var.Set.of_list
    |> Core.Set.to_list
  in
  let cf_sp =
    Option.value (List.find machine_reads ~f:is_sp) ~default:abi.Hike_abi.sp in
  { cf_lanes; cf_sp }

(* The static facts of one block.  In-place growth adds one of these to
   the same [rc_blocks] instead of rebuilding the context. *)
let block_facts_of_block ~(abi : Hike_abi.t) (b : blk term) : block_facts =
  let defs = Term.enum def_t b |> Seq.to_list in
  let def_index =
    List.foldi defs ~init:Var.Map.empty ~f:(fun pos index d ->
        Map.set index ~key:(Def.lhs d) ~data:(pos, d)) in
  {
    bf_term = b;
    bf_defs = defs;
    bf_def_index = def_index;
    bf_call_facts = call_facts_of_block ~abi b;
    bf_live_ids = Cbat_var_id.intern_set
        (Term.enum phi_t b |> Seq.map ~f:Phi.lhs |> Seq.to_list
         |> Var.Set.of_list);
  }

(* Preserved registers: the convention's SP plus its callee-saved GPRs. *)
let preserved_of_sub ~(abi : Hike_abi.t) (_s : sub term) : Int.Set.t =
  let regs =
    abi.Hike_abi.sp :: abi.Hike_abi.thread_pointer :: abi.callee_saved
    |> Var.Set.of_list in
  Cbat_var_id.intern_set regs

(* Per-sub static edge table: per (block, jmp) accumulated cond, in
   the completed (negation-free) form. *)
let edge_conds_of (sub : sub term) : exp Tid.Map.t Tid.Map.t =
  let ircfg = Sub.to_cfg sub in
  Graphs.Ir.edges ircfg
  |> Seq.fold ~init:Tid.Map.empty ~f:(fun acc e ->
      let src = Term.tid (Graphs.Ir.Node.label (Graphs.Ir.Edge.src e)) in
      let jmp = Term.tid (Graphs.Ir.Edge.jmp e) in
      let cond = Utils.complete_cond (Graphs.Ir.Edge.cond e ircfg) in
      Core.Map.update acc src ~f:(fun by_jmp ->
          Core.Map.set (Option.value by_jmp ~default:Tid.Map.empty)
            ~key:jmp ~data:cond))

(* Per-sub disabled-continuation table: each jmp observes the NEXT
   jmp's cond. *)
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

let mk_rctx ~(abi : Hike_abi.t) ~def_reads ~def_writes ~phi_writes:_
    ~jmp_reads
    ~(synth : Hike_synth.table ref)
    ?(sub_lookup : int64 -> Tid.t option = fun _ -> None)
    (s : sub term) : refine_ctx =
  let blocks =
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b)
          ~data:(block_facts_of_block ~abi b)) in
  let edge_conds = edge_conds_of s in
  {
    rc_edges = ref Tid.Map.empty;
    rc_nonneg = (fun ~env:_ _ -> false);
    rc_landmarks = Cbat_landmarks.create ();
    rc_abi = abi;
    rc_synth = synth;
    rc_sub_lookup = sub_lookup;
    rc_blocks = blocks;
    rc_preserved = preserved_of_sub ~abi s;
    rc_edge_conds = edge_conds;
    rc_disabled_conds = disabled_conds_of ~edge_conds s;
    rs_sub = s;
    rs_store = Tid.Map.empty;
    rs_default = AI.bottom;
    rs_incoming = Tid.Map.empty;
    rs_pending = Tid.Set.empty;
    rs_unplaced = Tid.Set.empty;
    rs_total_processed = 0;
    rs_head_visits = Hashtbl.create (module Tid);
    rs_current = None;
    rs_resolved = Tid.Map.empty;
    rs_reseed = Tid.Set.empty;
    rs_fan = Tid.Set.empty;
    rs_heads = Tid.Set.empty;
    rs_block_to_head = Hashtbl.create (module Tid);
    rs_dg = None;
    rs_wto = None;
    rs_smry = None;
    rs_need = None;
    rs_max_steps = None;
    rs_plan = None;
  }
