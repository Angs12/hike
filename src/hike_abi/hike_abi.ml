(* Sole home of target registers and calling-convention facts. *)

open Bap.Std
open Bap_core_theory
open Theory.Role.Register
open Bap.Std.Bil.Types

(* No frame-pointer fact: SP is the only register granted stack semantics;
   RBP is an ordinary callee-saved GPR. *)
type t = {
  sp : var;                      (* stack pointer *)
  thread_pointer : var;          (* the TLS base register *)
  int_param_regs : var list;     (* SysV integer/pointer arg registers *)
  vector_param_regs : var list;  (* FP/vector arg registers (YMM0-7) *)
  return_regs : var list;        (* integer return registers *)
  callee_saved : var list;       (* callee-saved GPRs (incl. RBP) *)
  caller_saved_gprs : var list;  (* GPRs a call may clobber (SysV) *)
  word : int;                    (* target word size in bytes *)
}

let x86_64_sysv : t =
  let r64 name = Var.create ~is_virtual:false ~fresh:false name (Type.Imm 64) in
  let r256 name = Var.create ~is_virtual:false ~fresh:false name (Type.Imm 256) in
  {
    sp = r64 "RSP";
    thread_pointer = r64 "FS_BASE";
    int_param_regs =
      Base.List.map ~f:r64 [ "RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9" ];
    vector_param_regs =
      Base.List.map ~f:r256
        (Base.List.map ~f:(fun i -> "YMM" ^ Base.Int.to_string i)
           (Base.List.range 0 8));
    return_regs = [ r64 "RAX"; r64 "RDX" ];
    callee_saved = Base.List.map ~f:r64 [ "RBX"; "RBP"; "R12"; "R13"; "R14"; "R15" ];
    caller_saved_gprs =
      Base.List.map ~f:r64
        [ "RAX"; "RCX"; "RDX"; "RSI"; "RDI"; "R8"; "R9"; "R10"; "R11" ];
    word = 8;
  }

(* Var-based predicates; [Var.same] compares base vars (EAX ~ RAX),
   [Var.equal] the full variable. *)
let is_sp (t : t) (v : var) : bool = Var.same v t.sp
let is_callee_saved (t : t) (v : var) : bool =
  Base.List.exists t.callee_saved ~f:(Var.same v)
let is_vector_param_reg (t : t) (v : var) : bool =
  Base.List.exists t.vector_param_regs ~f:(Var.same v)
let is_return_reg (t : t) (v : var) : bool =
  Base.List.exists t.return_regs ~f:(Var.same v)

(* Argument registers in convention order: integer, then vector. *)
let param_regs (t : t) : var list = t.int_param_regs @ t.vector_param_regs

let addr_size_bits target =
  if Theory.Target.is_unknown target then 0
  else Theory.Target.data_addr_size target

let sp target =
  match Theory.Target.reg target stack_pointer with
  | Some v -> Var.reify v
  | None -> x86_64_sysv.sp

let thread_pointer target =
  match Theory.Target.reg target thread with
  | Some v -> Var.reify v
  | None -> x86_64_sysv.thread_pointer

(* The one target the pipeline's facts are written against; unknown
   targets take the SysV fallback record. *)
let is_primary_target (t : Theory.Target.t) : bool =
  Theory.Target.matches t "x86_64-gnu-elf"

let pc target =
  if is_primary_target target then
    Var.create "RIP" (Imm (Theory.Target.data_addr_size target))
  else
    (* A synthetic RIP for var-equality tests on unknown targets. *)
    Var.create ~is_virtual:false ~fresh:false "RIP" (Type.Imm 64)

(* Consumers reach register lists and predicates only through here. *)

let of_target (target : Theory.Target.t) : t =
  (* The SysV record serves unknown targets. *)
  if is_primary_target target then
    {
      sp = sp target;
      thread_pointer = thread_pointer target;
      int_param_regs = x86_64_sysv.int_param_regs;
      vector_param_regs = x86_64_sysv.vector_param_regs;
      return_regs = x86_64_sysv.return_regs;
      callee_saved = x86_64_sysv.callee_saved;
      caller_saved_gprs = x86_64_sysv.caller_saved_gprs;
      word = Theory.Target.bits target / 8;
    }
  else x86_64_sysv

(* The target's word size in bits, from the byte size the record carries. *)
let word_bits (t : t) : int = 8 * t.word

(* SysV stack alignment: every stack object is 16-byte aligned. *)
let stack_align = 16

(* Value-register names for the FP-return detector. *)
let value_return_names = [ "RAX"; "EAX"; "RDX"; "EDX" ]

let is_value_return_reg (t : t) (v : var) : bool =
  Base.List.mem value_return_names (Var.name (Var.base v)) ~equal:String.equal

let vector_param_prefix = "YMM"