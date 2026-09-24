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

(* Mutable per-analysis state: the versioned solution values.  The
   fixpoint builds one per sub and the call abstraction one per callee
   — Tids are only unique per sub, so each context owns its own. *)
type fix_state = {
  (* Per-block solution values with their version stamps; a bump means
     the value changed. *)
  fs_sol : (AI.t * int) Tid.Map.t;
}

(* Static per-block facts, one per sub block: the block's term, the
   convention's integer-arg lanes the block writes plus the SP-push
   marker, and the may-read set at block entry (the GC keep-set). *)
type block_facts = {
  bf_term : blk term;
  bf_call_facts : var list * bool;
  bf_live_in : Var.Set.t;
}

type refine_ctx = {
  (* Mutable state, owned by this context. *)
  rc_state : fix_state;
  (* The last postcondition per source block, keyed physically by the
     entry state it was computed from: a k-successor pred denotes once
     per visit instead of once per edge. *)
  rc_post : (AI.t * AI.t) Tid.Map.t ref;
  (* The walked block's def chain with its pre/post states, keyed
     physically by the entry state the chain was denoted from. *)
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

let with_sol (rc : refine_ctx) (sol : (AI.t * int) Tid.Map.t) : refine_ctx =
  { rc with rc_state = { fs_sol = sol } }

(* Static per-block call facts: the convention's integer-arg lanes the
   block writes, and whether the block writes SP (the call-push marker). *)
let call_facts_of_block ~(abi : Hike_abi.t) (b : blk term) : var list * bool =
  let defs = Term.enum def_t b |> Seq.to_list in
  let written =
    List.filter abi.Hike_abi.int_param_regs ~f:(fun v ->
        List.exists defs ~f:(fun d -> Var.same (Def.lhs d) v)) in
  let rsp = abi.Hike_abi.sp in
  let pushed = List.exists defs ~f:(fun d -> Var.same (Def.lhs d) rsp) in
  (written, pushed)

(* Backward may-liveness over base-normalized vars. *)
let block_uses (b : blk term) : Var.Set.t =
  let base acc v = Core.Set.add acc (Var.base v) in
  let u =
    Core.Set.fold (Blk.free_vars b) ~init:Var.Set.empty
      ~f:(fun acc v -> base acc v) in
  Term.enum phi_t b
  |> Seq.fold ~init:u ~f:(fun acc ph ->
      Core.Set.fold (Phi.free_vars ph) ~init:acc
        ~f:(fun acc v -> base acc v))

(* Word-typed lhs vars defined in the block. *)
let block_defs (b : blk term) : Var.Set.t =
  Term.enum def_t b
  |> Seq.fold ~init:Var.Set.empty ~f:(fun acc d ->
      match Var.typ (Def.lhs d) with
      | Type.Imm _ -> Core.Set.add acc (Var.base (Def.lhs d))
      | Type.Mem _ | Type.Unk -> acc)

(* Live-in vars per block; fixpoint over successor unions. *)
let live_in_of_sub (s : sub term) (cfg : Graphs.Tid.t) :
    Var.Set.t Tid.Map.t =
  let blocks = Term.enum blk_t s |> Seq.to_list in
  let find m tid =
    Option.value ~default:Var.Set.empty (Core.Map.find m tid) in
  let uses =
    List.fold blocks ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b) ~data:(block_uses b)) in
  let defs =
    List.fold blocks ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b) ~data:(block_defs b)) in
  let live = ref Tid.Map.empty in
  let rec loop () =
    let changed = ref false in
    List.iter (List.rev blocks) ~f:(fun b ->
        let bt = Term.tid b in
        let out =
          Graphs.Tid.Node.succs bt cfg |> Seq.fold ~init:Var.Set.empty
            ~f:(fun acc t -> Core.Set.union acc (find !live t)) in
        let inn =
          Core.Set.union (find uses bt)
            (Core.Set.diff out (find defs bt)) in
        if not (Core.Set.equal inn (find !live bt)) then begin
          live := Core.Map.set !live ~key:bt ~data:inn;
          changed := true
        end);
    if !changed then loop () in
  loop ();
  !live

(* The per-run analysis context: one fold over the sub's blocks builds
   the per-block fact records; the live-in fixpoint feeds them. *)
let mk_rctx ~(cfg : Graphs.Tid.t) ~(abi : Hike_abi.t)
    ?(sub_lookup : int64 -> Tid.t option = fun _ -> None)
    (s : sub term) : refine_ctx = {
  rc_nonneg = (fun ~env:_ _ -> false);
  rc_landmarks = Cbat_landmarks.create ();
  rc_state = {
    fs_sol = Tid.Map.empty;
  };
  rc_post = ref Tid.Map.empty;
  rc_prefix = ref Tid.Map.empty;
  rc_abi = abi;
  rc_sub_lookup = sub_lookup;
  rc_blocks =
    let live = live_in_of_sub s cfg in
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b)
          ~data:{
            bf_term = b;
            bf_call_facts = call_facts_of_block ~abi b;
            bf_live_in =
              Option.value ~default:Var.Set.empty
                (Core.Map.find live (Term.tid b)) });
}

let ver_of (rc : refine_ctx) (t : Tid.t) : int =
  Option.value_map (Core.Map.find rc.rc_state.fs_sol t) ~default:0 ~f:snd
