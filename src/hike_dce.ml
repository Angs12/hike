(* Dead-code elimination for the hike pipeline. Replaces the lifted return epilogue (indirect noreturn call) with a var-free form, then iteratively removes defs whose lhs is never used. Memory writes and ABI registers are always kept.
   RSP erasure on the precise path uses BAP-derived SP (Targetutils.sp), not hardcoded strings.
   RBP is not explicitly erased; it is deleted by the fixpoint if derived from RSP (RBP:=RSP) and RSP is erased. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory

(* ABI registers that may be read implicitly by calls. *)
let is_ret_reg (v : var) : bool =
  Base.List.exists Calling_conventions.x86_64_sysv.return_regs
    ~f:(fun r -> Var.same r (Var.base v))

let is_call_reg (v : var) : bool =
  let regs =
    Calling_conventions.x86_64_sysv.param_regs
    @ Calling_conventions.x86_64_sysv.return_regs
  in
  Base.List.exists regs ~f:(fun r -> Var.same r (Var.base v))

(* Replace an indirect noreturn call (return idiom) with a var-free target. *)
let ret_replacement (j : jmp term) : jmp term =
  match Jmp.kind j with
  | Call c -> (
      match (Call.target c, Call.return c) with
      | Indirect (Bil.Var _), None ->
          Jmp.create ~tid:(Term.tid j) ~cond:(Jmp.cond j)
            (Call
               (Call.create
                  ~target:
                    (Indirect (Bil.Unknown ("hike-dce-ret", Type.Imm 64)))
                  ()))
      | _ -> j)
  | _ -> j

(* Vars referenced by any def, jmp, or phi in the sub. *)
let used_of (sub : sub term) : Var.Set.t =
  let v =
    object
      inherit [Var.Set.t] Term.visitor
      method! visit_def d used = Core.Set.union used (Def.free_vars d)
      method! visit_jmp j used = Core.Set.union used (Jmp.free_vars j)
      method! visit_phi p used = Core.Set.union used (Phi.free_vars p)
    end
  in
  v#visit_sub sub Var.Set.empty

(* FP intrinsic interface vars ([intrinsic:xN] / [intrinsic:yN]). *)
let is_intrinsic_var (v : var) : bool =
  Base.String.is_prefix (Var.name (Var.base v)) ~prefix:"intrinsic:"

let is_hike_stack (v : var) : bool = Var.same v Convutils.hike_stack_var

let is_sp (target : Theory.Target.t) (v : var) : bool =
  Var.same v (Targetutils.sp target)

let rec sp_value_exp (target : Theory.Target.t) (e : exp) : bool =
  match e with
  | Bil.Var v -> is_sp target v
  | Bil.BinOp (_, a, b) -> sp_value_exp target a || sp_value_exp target b
  | Bil.UnOp (_, a) -> sp_value_exp target a
  | Bil.Cast (_, _, a) -> sp_value_exp target a
  | Bil.Extract (_, _, a) -> sp_value_exp target a
  | Bil.Concat (a, b) -> sp_value_exp target a || sp_value_exp target b
  | Bil.Let (_, a, b) -> sp_value_exp target a || sp_value_exp target b
  | Bil.Ite (c, a, b) -> sp_value_exp target c || sp_value_exp target a || sp_value_exp target b
  | _ -> false

let is_sp_value_def (target : Theory.Target.t) (d : def term) : bool =
  not (Convutils.is_mem (Def.lhs d))
  && not (is_sp target (Var.base (Def.lhs d)))
  && sp_value_exp target (Def.rhs d)

let is_sp_for_erasure (target : Theory.Target.t) (d : def term) : bool =
  is_sp target (Def.lhs d)

(* Precise predicate for RSP erasure (ADR 0001 Q1/A, Q2): the sub uses the
   SPLIT stack model (per-region [stack_rN] allocas) — its SP/hike_stack
   defs are dead.

   Finding 1: the decision is READ from [Convutils.stack_plan], the single
   result [Hike_stack_to_locals.split_plan] produced in the vsa pass. This
   pass is a CONSUMER — it no longer imports the emitter's
   [region_split_plan] to re-derive a BIL-level fact. *)
let is_precise_sub (_target : Theory.Target.t) (sub : sub term) : bool =
  match Core.Map.find (Hike_kb.vsa_info ()) (Term.tid sub) with
  | None -> false
  | Some info -> Hike_stack_to_locals.is_precise info

let keep ?(precise=false) ~target (d : def term) (used : Var.Set.t) : bool =
  if precise && (is_sp_for_erasure target d || is_hike_stack (Def.lhs d) || is_sp_value_def target d) then false
  else
    let lhs = Def.lhs d in
    Core.Set.mem used lhs || is_ret_reg lhs || Convutils.is_mem lhs
    || is_call_reg lhs || is_intrinsic_var lhs

let def_count (sub : sub term) : int =
  Term.enum blk_t sub
  |> Seq.fold ~init:0 ~f:(fun n blk ->
      n + Seq.length (Term.enum def_t blk))

(* Iteratively remove unused defs until fixpoint. For precise subs, SP/hike_stack/sp_value are dead (Q2, Q5). *)
let rec sweep_fixpoint ~target (sub : sub term) : sub term =
  let precise = is_precise_sub target sub in
  let used = used_of sub in
  let sub' =
    Term.map blk_t sub ~f:(fun blk ->
        Term.filter def_t blk ~f:(fun d -> keep ~precise ~target d used))
  in
  if def_count sub' = def_count sub then sub' else sweep_fixpoint ~target sub'

(* Run DCE: rewrite return calls, then sweep unused defs. Intrinsics are left unchanged. *)
let dce ~target (sub : sub term) : sub term =
  if Term.has_attr sub Sub.intrinsic then sub
  else
    let mapper =
      object
        inherit Term.mapper
        method! map_jmp j = ret_replacement j
      end
    in
    mapper#map_sub sub |> sweep_fixpoint ~target
