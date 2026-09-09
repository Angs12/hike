(* Sole home of target registers and calling-convention facts. *)

open Bap.Std
open Bap_core_theory
open Theory.Role.Register
open Bap.Std.Bil.Types

(* Convention record.  There is NO frame-pointer fact: RBP is an ordinary
   callee-saved GPR (ADR 0008 — SP is the only register granted stack
   semantics by fiat). *)
type t = {
  sp : var;                      (* stack pointer *)
  int_param_regs : var list;     (* SysV integer/pointer arg registers *)
  vector_param_regs : var list;  (* FP/vector arg registers (YMM0-7) *)
  return_regs : var list;        (* integer return registers *)
  callee_saved : var list;       (* callee-saved GPRs (incl. RBP) *)
}

let param_regs t = t.int_param_regs @ t.vector_param_regs

let x86_64_sysv : t =
  let r64 name = Var.create ~is_virtual:false ~fresh:false name (Type.Imm 64) in
  let r256 name = Var.create ~is_virtual:false ~fresh:false name (Type.Imm 256) in
  {
    sp = r64 "RSP";
    int_param_regs =
      Base.List.map ~f:r64 [ "RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9" ];
    vector_param_regs =
      Base.List.map ~f:r256
        (Base.List.map ~f:(fun i -> "YMM" ^ Base.Int.to_string i)
           (Base.List.range 0 8));
    return_regs = [ r64 "RAX"; r64 "RDX" ];
    callee_saved = Base.List.map ~f:r64 [ "RBX"; "RBP"; "R12"; "R13"; "R14"; "R15" ];
  }

(* Var-based predicates; Var.same compares names. *)
let is_sp (t : t) (v : var) : bool = Var.same v t.sp
let is_callee_saved (t : t) (v : var) : bool =
  Base.List.exists t.callee_saved ~f:(Var.same v)
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

let pc target =
  if Theory.Target.matches target "x86_64-gnu-elf" then
    Var.create "RIP" (Imm (Theory.Target.data_addr_size target))
  else
    (* Total on unknown targets: a synthetic RIP for var-equality tests. *)
    Var.create ~is_virtual:false ~fresh:false "RIP" (Type.Imm 64)

(* Only consumers reach register lists or predicates through here. *)

(* x86_64-gnu-elf only. of_target_opt is total (None on unknown targets). *)
let of_target_opt (target : Theory.Target.t) : t option =
  if Theory.Target.matches target "x86_64-gnu-elf" then
    Some
      {
        sp = sp target;
        int_param_regs = x86_64_sysv.int_param_regs;
        vector_param_regs = x86_64_sysv.vector_param_regs;
        return_regs = x86_64_sysv.return_regs;
        callee_saved = x86_64_sysv.callee_saved;
      }
  else None

let of_target (target : Theory.Target.t) : t =
  (* Total: the SysV record serves unknown targets (unit fixtures). *)
  Option.value (of_target_opt target) ~default:x86_64_sysv

let param_regs target = param_regs (of_target target)

(* Value-register names for the FP-return detector. *)
let value_return_names = [ "RAX"; "EAX"; "RDX"; "EDX" ]

(* Vector-register name prefix. *)
let vector_param_prefix = "YMM"