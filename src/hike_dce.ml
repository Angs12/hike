(* Sweeps dead defs; region mems survive iff loaded. *)

open Bap.Std
open Bap.Std.Bil.Types
open Bap_core_theory
module Abi = Hike_abi

(* ABI record, defaulting to x86_64 SysV. *)
let abi_of (target : Theory.Target.t) : Abi.t =
  Option.value (Abi.of_target_opt target) ~default:Abi.x86_64_sysv

(* Stack pointer, defaulting to the record's. *)
let sp_of (target : Theory.Target.t) : var =
  match Abi.sp target with
  | v -> v
  | exception _ -> (abi_of target).Abi.sp

(* Registers read implicitly by calls. *)
let is_ret_reg (target : Theory.Target.t) (v : var) : bool =
  Abi.is_return_reg (abi_of target) (Var.base v)

let is_call_reg (target : Theory.Target.t) (v : var) : bool =
  let abi = abi_of target in
  let regs = abi.Abi.int_param_regs @ abi.Abi.vector_param_regs @ abi.Abi.return_regs in
  Base.List.exists regs ~f:(fun r -> Var.same r (Var.base v))

(* Rewrites the return epilogue to a var-free target. *)
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

(* Tests for region mem vars. *)
let is_region_mem (v : var) : bool =
  Hike_stack_model.is_region_mem v

(* Vars read as Load mem operands, plus jmp/phi reads. *)

let load_roots_of (sub : sub term) : Var.Set.t =
  let roots =
    object
      inherit [Var.Set.t] Term.visitor
      method! visit_load ~mem ~addr:_ _ _ acc =
        Core.Set.union acc (Exp.free_vars mem)
      
      method! visit_jmp j acc = Core.Set.union acc (Jmp.free_vars j)
      method! visit_phi p acc = Core.Set.union acc (Phi.free_vars p)
    end
  in
  roots#visit_sub sub Var.Set.empty

(* Vars used by any def, jmp, or phi. *)
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

(* Tests for intrinsic interface vars. *)
let is_intrinsic_var (v : var) : bool =
  Convutils.is_intrinsic_name (Var.name (Var.base v))

let is_hike_stack (v : var) : bool = Var.same v Convutils.hike_stack_var

let is_sp (target : Theory.Target.t) (v : var) : bool =
  Var.same v (sp_of target)

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

(* True when the sub uses the split model. *)
let is_precise_sub (_target : Theory.Target.t) (sub : sub term) : bool =
  match Core.Map.find (Hike_kb.vsa_info ()) (Term.tid sub) with
  | None -> false
  | Some info -> Hike_stack_model.is_precise info

(* Region mems survive iff loaded; [mem] always survives. *)
let keep ?(precise=false) ?(load_roots=Var.Set.empty)
    ~target (d : def term) (used : Var.Set.t) : bool =
  if precise && (is_sp_for_erasure target d || is_hike_stack (Def.lhs d) || is_sp_value_def target d) then false
  else
    let lhs = Def.lhs d in
    if is_region_mem lhs then
      Core.Set.mem load_roots lhs
      
    else
      Core.Set.mem used lhs || is_ret_reg target lhs || Convutils.is_mem lhs
      || is_call_reg target lhs || is_intrinsic_var lhs

let def_count (sub : sub term) : int =
  Term.enum blk_t sub
  |> Seq.fold ~init:0 ~f:(fun n blk ->
      n + Seq.length (Term.enum def_t blk))

(* Sweeps unused defs to fixpoint. *)
let rec sweep_fixpoint ~target (sub : sub term) : sub term =
  let precise = is_precise_sub target sub in
  let used = used_of sub in
  
  let load_roots = load_roots_of sub in
  let sub' =
    Term.map blk_t sub ~f:(fun blk ->
        Term.filter def_t blk ~f:(fun d ->
            keep ~precise ~load_roots ~target d used))
  in
  if def_count sub' = def_count sub then sub' else sweep_fixpoint ~target sub'

(* Rewrites returns, then sweeps. Intrinsics pass through. *)
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
