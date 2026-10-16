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

(* Static per-block facts, one per sub block: the block's term, the
   convention's integer-arg lanes the block writes plus the SP-push
   marker, and the may-read set at block entry (the GC keep-set). *)
type block_facts = {
  bf_term : blk term;
  bf_call_facts : var list * bool;
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
     the walk anchors on, the call-written register lanes, and the
     word size behind every word lookup. *)
  rc_abi : Hike_abi.t;
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

(* Static per-block call facts: the convention's integer-arg lanes the
   block writes, and whether the block's call pushes a return address
   (a machine call with a return; an intrinsic is rendered inline and a
   no-return transfer is a tail, so neither pushes). *)
let call_facts_of_block ~(abi : Hike_abi.t) ~def_writes (b : blk term) :
    var list * bool =
  let defs = Term.enum def_t b |> Seq.to_list in
  let written =
    List.filter abi.Hike_abi.int_param_regs ~f:(fun v ->
        List.exists defs ~f:(fun d -> Core.Set.mem (def_writes d) v)) in
  let pushed =
    Term.enum jmp_t b
    |> Seq.exists ~f:(fun j ->
           match Jmp.kind j with
           | Call c -> (
               Option.is_some (Call.return c)
               && (match Call.target c with
                   | Indirect _ -> true
                   | Direct t -> not (Hike_abi.is_intrinsic_target t)))
           | _ -> false)
  in
  (written, pushed)

(* Backward may-liveness over base-normalized vars. *)
let base_vars vars =
  Core.Set.fold vars ~init:Var.Set.empty ~f:(fun acc v ->
      Core.Set.add acc (Var.base v))

let live_in_of_sub ~def_reads ~def_writes ~phi_reads
    ~phi_writes:_ ~jmp_reads (s : sub term) =
  (* Only an immediate def kills; a memory def and every phi leave the
     live set alone. *)
  let def d =
    let kill =
      match Var.typ (Def.lhs d) with
      | Type.Imm _ -> base_vars (def_writes d)
      | Type.Mem _ | Type.Unk -> Var.Set.empty
    in
    (kill, base_vars (def_reads d))
  in
  let phi p = (Var.Set.empty, base_vars (phi_reads p)) in
  let jmp j = base_vars (jmp_reads j) in
  Hike_bir_flow.liveness ~graph:(Sub.to_graph s) ~sub:s
    ~initial:(Tid.Map.singleton Graphs.Tid.exit Var.Set.empty)
    ~def ~phi ~jmp

(* The per-run analysis context: one fold over the sub's blocks builds
   the per-block fact records; the live-in fixpoint feeds them. *)
let mk_rctx ~(abi : Hike_abi.t) ~def_reads ~def_writes ~phi_reads ~phi_writes
    ~jmp_reads
    ?(sub_lookup : int64 -> Tid.t option = fun _ -> None)
    (s : sub term) : refine_ctx = {
  rc_nonneg = (fun ~env:_ _ -> false);
  rc_landmarks = Cbat_landmarks.create ();
  rc_post = ref Tid.Map.empty;
  rc_prefix = ref Tid.Map.empty;
  rc_abi = abi;
  rc_sub_lookup = sub_lookup;
  rc_blocks =
    let live =
      live_in_of_sub ~def_reads ~def_writes ~phi_reads ~phi_writes
        ~jmp_reads s
    in
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b)
          ~data:{
            bf_term = b;
            bf_call_facts = call_facts_of_block ~abi ~def_writes b;
            bf_live_ids =
              Cbat_var_id.intern_set
                (Option.value ~default:Var.Set.empty
                   (Core.Map.find live.before (Term.tid b))) });
}
