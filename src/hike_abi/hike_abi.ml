(* Sole home of target registers and calling-convention facts. *)

open Bap.Std
open Bap_core_theory
open Theory.Role.Register
open Bap.Std.Bil.Types

(* Convention record. *)
type t = {
  sp : var;                      (* stack pointer *)
  fp : var;                      (* frame pointer *)
  int_param_regs : var list;     (* SysV integer/pointer arg registers *)
  vector_param_regs : var list;  (* FP/vector arg registers (YMM0-7) *)
  return_regs : var list;        (* integer return registers *)
  callee_saved : var list;       (* callee-saved GPRs; RBP carried as [fp] *)
}

let param_regs t = t.int_param_regs @ t.vector_param_regs

let x86_64_sysv : t =
  let r64 name = Var.create ~is_virtual:false ~fresh:false name (Type.Imm 64) in
  let r256 name = Var.create ~is_virtual:false ~fresh:false name (Type.Imm 256) in
  {
    sp = r64 "RSP";
    fp = r64 "RBP";
    int_param_regs =
      Base.List.map ~f:r64 [ "RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9" ];
    vector_param_regs =
      Base.List.map ~f:r256
        (Base.List.map ~f:(fun i -> "YMM" ^ Base.Int.to_string i)
           (Base.List.range 0 8));
    return_regs = [ r64 "RAX"; r64 "RDX" ];
    callee_saved = Base.List.map ~f:r64 [ "RBX"; "R12"; "R13"; "R14"; "R15" ];
  }

(* Var-based predicates; Var.same compares names. *)
let is_sp (t : t) (v : var) : bool = Var.same v t.sp
let is_fp (t : t) (v : var) : bool = Var.same v t.fp
let is_stack_reg (t : t) (v : var) : bool = is_sp t v || is_fp t v
let is_callee_saved (t : t) (v : var) : bool =
  Base.List.exists t.callee_saved ~f:(Var.same v)
let is_preserved (t : t) (v : var) : bool =
  is_stack_reg t v || is_callee_saved t v
(* Structural model-ABI lanes; never-defined reads here aggregate per-sub. *)
let is_vector_param_reg (t : t) (v : var) : bool =
  Base.List.exists t.vector_param_regs ~f:(Var.same v)
let is_return_reg (t : t) (v : var) : bool =
  Base.List.exists t.return_regs ~f:(Var.same v)

(* Target-derived registers and sizes. *)

let addr_size_bits target =
  if Theory.Target.is_unknown target then 0
  else Theory.Target.data_addr_size target

let sp target =
  match Theory.Target.reg target stack_pointer with
  | Some v -> Var.reify v
  | None -> x86_64_sysv.sp

let fp target =
  match Theory.Target.reg target frame_pointer with
  | Some v -> Var.reify v
  | None -> x86_64_sysv.fp

let pc target =
  if Theory.Target.matches target "x86_64-gnu-elf" then
    Var.create "RIP" (Imm (Theory.Target.data_addr_size target))
  else
    (* Total on unknown targets: a synthetic RIP for var-equality tests. *)
    Var.create ~is_virtual:false ~fresh:false "RIP" (Type.Imm 64)

let resolve_alias target reg =
  let sort = Var.sort reg in
  let name = Var.name reg in
  let theory_var = Theory.Var.define sort name in
  Option.bind (Theory.Target.unalias target theory_var) Theory.Origin.cast_sub

let theory_regs target = Theory.Target.regs target |> Base.Set.to_list

let base_regs target =
  theory_regs target
  |> Base.List.filter ~f:(fun reg ->
      Option.is_none (Theory.Target.unalias target reg))
  |> Base.List.map ~f:Var.reify

(* Only consumers reach register lists or predicates through here. *)

let imm width = Imm width
let r64 name = Var.create name (imm 64)
let r256 name = Var.create name (imm 256)

(* x86_64-gnu-elf only. of_target_opt is total (None on unknown targets). *)
let of_target_opt (target : Theory.Target.t) : t option =
  if Theory.Target.matches target "x86_64-gnu-elf" then
    Some
      {
        sp = sp target;
        fp = fp target;
        int_param_regs = x86_64_sysv.int_param_regs;
        vector_param_regs = x86_64_sysv.vector_param_regs;
        return_regs = x86_64_sysv.return_regs;
        callee_saved = x86_64_sysv.callee_saved;
      }
  else None

let of_target (target : Theory.Target.t) : t =
  (* Total: the SysV record serves unknown targets (unit fixtures). *)
  Option.value (of_target_opt target) ~default:x86_64_sysv

let int_param_regs target = (of_target target).int_param_regs
let vector_param_regs target = (of_target target).vector_param_regs
let param_regs target = param_regs (of_target target)
let return_regs target = (of_target target).return_regs
let callee_saved target = (of_target target).callee_saved

let is_sp_t target v = is_sp (of_target target) v
let is_fp_t target v = is_fp (of_target target) v
let is_sp_or_fp_t target v = is_stack_reg (of_target target) v
let is_callee_saved_t target v = is_callee_saved (of_target target) v

(* Value-register names for the FP-return detector. *)
let value_return_names = [ "RAX"; "EAX"; "RDX"; "EDX" ]

(* Vector-register name prefix. *)
let vector_param_prefix = "YMM"