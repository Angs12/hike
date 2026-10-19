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

(* Static per-block facts, one per sub block: the block's term, its call
   facts, and the may-read set at block entry plus its phi lhs's (the GC
   keep-set). *)
type block_facts = {
  bf_term : blk term;
  bf_call_facts : call_facts;
  bf_live_ids : Int.Set.t;
}

type refine_ctx = {
  (* The last postcondition per source block, keyed physically by the
     entry state it was computed from: a k-successor pred denotes once
     per visit instead of once per edge. *)
  rc_post : (AI.t * AI.t) Tid.Map.t ref;
  (* The walked block's def chain with its pre/post states, keyed
     physically by the entry state the chain was denoted from: the
     postcondition fold, the writer and the observer all enter with the
     block's IN state, so one chain serves them. *)
  rc_prefix : (AI.t * (def term * AI.t * AI.t) list) Tid.Map.t ref;
  (* The run's convention facts (Hike_abi is the one home): the sp var
     the walk anchors on, the call-read lanes, and the
     word size behind every word lookup. *)
  rc_abi : Hike_abi.t;
  rc_synth : Hike_synth.table ref;
  rc_blocks : block_facts Tid.Map.t;
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

(* Backward may-liveness over exact vars: a phi kills its lhs, and its
   operands are live at the end of the predecessor they come from. *)
let live_in_of_sub ~def_reads ~def_writes ~phi_writes ~jmp_reads
    (s : sub term) =
  (* Only an immediate def kills; a memory def leaves the live set
     alone. *)
  let def d =
    let kill =
      match Var.typ (Def.lhs d) with
      | Type.Imm _ -> def_writes d
      | Type.Mem _ | Type.Unk -> Var.Set.empty
    in
    (kill, def_reads d)
  in
  let phi p = (phi_writes p, Var.Set.empty) in
  let operands_of =
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Term.enum phi_t b
        |> Seq.fold ~init:m ~f:(fun m p ->
            Seq.fold (Phi.values p) ~init:m ~f:(fun m (src, e) ->
                Core.Map.update m src ~f:(fun vs ->
                    Core.Set.union
                      (Option.value vs ~default:Var.Set.empty)
                      (Exp.free_vars e)))))
  in
  (* A block's jumps end it, so they carry its outgoing phi operands. *)
  let jmp_operands =
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        match Core.Map.find operands_of (Term.tid b) with
        | None -> m
        | Some vs ->
          Term.enum jmp_t b
          |> Seq.fold ~init:m ~f:(fun m j ->
              Core.Map.set m ~key:(Term.tid j) ~data:vs))
  in
  let jmp j =
    ( Var.Set.empty,
      Core.Set.union (jmp_reads j)
        (Option.value (Core.Map.find jmp_operands (Term.tid j))
           ~default:Var.Set.empty) )
  in
  Hike_bir_flow.liveness ~graph:(Sub.to_graph s) ~sub:s
    ~initial:(Tid.Map.singleton Graphs.Tid.exit Var.Set.empty)
    ~def ~phi ~jmp

(* The per-run analysis context: one fold over the sub's blocks builds
   the per-block fact records; the live-in fixpoint feeds them. *)
let mk_rctx ~(abi : Hike_abi.t) ~def_reads ~def_writes ~phi_writes
    ~jmp_reads
    ~(synth : Hike_synth.table ref)
    ?(sub_lookup : int64 -> Tid.t option = fun _ -> None)
    (s : sub term) : refine_ctx = {
  rc_nonneg = (fun ~env:_ _ -> false);
  rc_landmarks = Cbat_landmarks.create ();
  rc_post = ref Tid.Map.empty;
  rc_prefix = ref Tid.Map.empty;
  rc_abi = abi;
  rc_synth = synth;
  rc_sub_lookup = sub_lookup;
  rc_blocks =
    let live =
      live_in_of_sub ~def_reads ~def_writes ~phi_writes ~jmp_reads s
    in
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b)
          ~data:{
            bf_term = b;
            bf_call_facts = call_facts_of_block ~abi b;
            bf_live_ids =
              Cbat_var_id.intern_set
                (Core.Set.union
                   (Option.value ~default:Var.Set.empty
                      (Core.Map.find live.before (Term.tid b)))
                   (Term.enum phi_t b |> Seq.map ~f:Phi.lhs |> Seq.to_list
                    |> Var.Set.of_list)) });
}
