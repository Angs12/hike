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


(* Per-run analysis context: static per-block facts, version stamps and
   walk/transfer memos threaded through the engine. *)

open Core_kernel
open Bap.Std
open Graphlib.Std
module Abi = Hike_abi
module Utils = Cbat_vsa_utils
module AI = Cbat_ai_representation

(* The walk's default pop cap and the per-edge budget unit (spec §2.1/§2.2). *)
let cap_default = 256
let budget_per_edge = 1024

(* Version-keyed memos for walk and transfer. *)



module Walk_memo = Cbat_memo.Make (struct
  type t = AI.t
end)


(* Per-block flag group. *)
type flag_group = {
  flags : (var * def term) Var.Map.t;
  (* 1-bit defs by base lhs. *)
  cmp : def term option;
  (* Record def by structural equality. *)
}


(* Per-run analysis context. *)
(* Mutable per-analysis state: the solution values, the version counters
   that key the memos, and the memos themselves.

   This lives INSIDE [refine_ctx] rather than at module level because there
   is more than one context: the fixpoint builds one per sub and the call
   abstraction builds a fresh one per callee. Sharing memo entries between
   them would be unsound — different subs reuse the same Tid keys for
   different blocks. Each context owns its own. *)
type fix_state = {
  (* Per-block solution values. *)
  fs_sol : AI.t Tid.Map.t;
  (* Per-block versions; a bump means the value changed. *)
  fs_versions : int Tid.Map.t;
  (* Cached walks. *)
  fs_cache : Walk_memo.t;
}

type refine_ctx = {
  (* Mutable state, owned by this context. *)
  rc_state : fix_state;
  (* Walk CFG without pseudo-nodes. *)
  rc_walk_cfg : Graphs.Tid.t;
  (* Per-block flag states. *)
  rc_flag_states :
    ((var * Bil.binop * exp * word) option * flag_group) Tid.Map.t;
  (* Per-block call facts. *)
  rc_call_facts : (var list * bool) Tid.Map.t;
  (* May-read vars per block entry; the GC keep-sets. *)
  rc_live_in : Var.Set.t Tid.Map.t;
  (* Per-SCC walk-pop budget; the ref shares one cell across ctx copies. *)
  rc_walk_budget : int ref;
  (* Per-block jmp out-edge counts; the budget allowance input. *)
  rc_out_edges : int Tid.Map.t;
  (* Block terms by tid; the walk's per-pop lookup (a linear Term.find
     over the sub, ~95M Tid compares per heavy sub). *)
  rc_blocks : blk term Tid.Map.t;
}

(* Record-update helpers: the triple-nested ctx/state updates in one
   place, used by every memo/transfer update site. *)
let with_cache (rc : refine_ctx) (cache : Walk_memo.t) : refine_ctx =
  { rc with rc_state = { rc.rc_state with fs_cache = cache } }

let with_sol ?(versions : int Tid.Map.t option = None) (rc : refine_ctx)
    (sol : AI.t Tid.Map.t) : refine_ctx =
  { rc with
    rc_state =
      { rc.rc_state with
        fs_sol = sol;
        fs_versions =
          Option.value ~default:rc.rc_state.fs_versions versions } }

(* Last understood flag-setting comparison. *)


let flag_state_of_block (b : blk term) :
    (var * Bil.binop * exp * word) option * flag_group =
  let ds = Term.enum def_t b |> Seq.to_list in
  let understood (op : Bil.binop) : bool =
    match op with
    | Bil.LT | Bil.LE | Bil.EQ | Bil.SLT | Bil.SLE -> true
    | _ -> false in
  let rec go (st : (var * Bil.binop * exp * word) option)
      (ds : def term list) : (var * Bil.binop * exp * word) option =
    match ds with
    | [] -> st
    | d :: rest ->
      let lhs = Def.lhs d in
      let lhs_base = Var.base lhs in
      (* Operand clobber clears. *)
      let st =
        match st with
        | Some (fv, op, e, c)
          when Exp.free_vars e |> Core.Set.exists ~f:(fun x ->
              Var.same x lhs_base) ->
          None
        | _ -> st in
      (* Flag rebinds or clears. *)
      let st =
        match st, Var.typ lhs, Def.rhs d with
        | Some (fv, _, _, _), Type.Imm 1, Bil.BinOp (op', e', Bil.Int c') ->
          if Var.same fv lhs_base then
            (if understood op' then Some (lhs, op', e', c') else None)
          else st
        | Some (fv, _, _, _), Type.Imm 1, _ ->
          if Var.same fv lhs_base then None else st
        | None, Type.Imm 1, Bil.BinOp (op', e', Bil.Int c') ->
          if understood op' then Some (lhs, op', e', c') else None
        | _ -> st in
      go st rest
  in
  let record = go None ds in
  (* 1-bit defs by base. *)
  let flags =
    Term.enum def_t b
    |> Seq.fold ~init:Var.Map.empty ~f:begin fun g d ->
      let lhs = Def.lhs d in
      match Var.typ lhs with
      | Type.Imm 1 -> Core.Map.set g ~key:(Var.base lhs) ~data:(lhs, d)
      | Type.Imm _ | Type.Mem _ | Type.Unk -> g
    end in
  (* Record def; temp or inline shape. *)
  let cmp =
    match record with
    | None -> None
    | Some (_, _, e, c) ->
      let temp_shape (d : def term) : bool =
        match Def.rhs d with
        | Bil.BinOp (Bil.MINUS, e', Bil.Int c') ->
          Exp.equal e' e && Word.equal c' c
        | _ -> false in
      let inline_shape (d : def term) : bool =
        match Def.rhs d with
        | Bil.BinOp ((Bil.EQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE), e', Bil.Int c') ->
          Exp.equal e' e && Word.equal c' c
        | _ -> false in
      match List.find ds ~f:temp_shape with
      | Some d -> Some d
      | None -> List.find ds ~f:inline_shape in
  (record, { flags; cmp })


(* Same-comparison gate. *)
let same_comparison_group (fg : flag_group) (fv : var) (e : exp)
    (cond : exp) : bool =
  (* True for flag vars. *)
  let is_flag (v : var) : bool =
    match Var.name v with
    | "CF" | "ZF" | "SF" | "OF" -> true
    | _ -> false in
  (* Flags in cond plus the record flag. *)
  let flag_vars =
    Exp.free_vars cond
    |> Core.Set.fold ~init:Var.Set.empty ~f:begin fun acc v ->
      if is_flag v then Core.Set.add acc (Var.base v) else acc
    end in
  let flag_vars =
    if is_flag fv then Core.Set.add flag_vars (Var.base fv)
    else flag_vars in
  match fg.cmp with
  | None -> false
  | Some td ->
    let t = Def.lhs td in
    let fvs_e = Exp.free_vars e in
    Core.Set.for_all flag_vars ~f:begin fun v ->
      match Core.Map.find fg.flags v with
      | None -> false
      | Some (_, d) ->
        Exp.free_vars (Def.rhs d)
        |> Core.Set.for_all ~f:begin fun w ->
          (* Base-equal free vars. *)
          Core.Set.exists fvs_e ~f:(fun x -> Var.same w x)
          || Var.same w t
        end
    end


(* Static per-block call facts. *)
let call_facts_of_block (b : blk term) : var list * bool =
  let defs = Term.enum def_t b |> Seq.to_list in
  let written =
    List.filter Abi.x86_64_sysv.int_param_regs ~f:(fun v ->
        List.exists defs ~f:(fun d -> Var.same (Def.lhs d) v)) in
  let rsp = Abi.x86_64_sysv.sp in
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

(* Count of a block's control-transfer out-edges; the walk-budget
   allowance input. Every jmp kind carries a target (a conditional
   block's guard jump and fallthrough both count — that is the CFG
   out-degree of the block). *)
let out_edge_count_of_block (b : blk term) : int =
  Term.enum jmp_t b
  |> Seq.fold ~init:0 ~f:(fun acc j ->
      match Jmp.kind j with
      | Goto _ | Ret _ | Call _ | Int _ -> acc + 1)

(* Block version; 0 means never set. *)
(* Per-run analysis context. *)
let mk_rctx ~(cfg : Graphs.Tid.t) (s : sub term) : refine_ctx = {
  rc_state = {
    fs_sol = Tid.Map.empty;
    fs_versions = Tid.Map.empty;
    fs_cache = Walk_memo.empty;
  };
  rc_walk_cfg = cfg;
  rc_flag_states =
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b) ~data:(flag_state_of_block b));
  rc_call_facts =
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b) ~data:(call_facts_of_block b));
  rc_live_in = live_in_of_sub s cfg;
  (* Unused until the first per-SCC recharge sets it. *)
  rc_walk_budget = ref max_int;
  rc_out_edges =
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b)
          ~data:(out_edge_count_of_block b));
  rc_blocks =
    Term.enum blk_t s
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun m b ->
        Core.Map.set m ~key:(Term.tid b) ~data:b);
}

let ver_of (rc : refine_ctx) (t : Tid.t) : int =
  match Core.Map.find rc.rc_state.fs_versions t with
  | Some v -> v
  | None -> 0
