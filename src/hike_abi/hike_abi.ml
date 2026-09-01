(* Abi — THE single home of target-derived registers and calling-convention
   facts (AGENTS.md Principle 8: never hardcode a register name outside this
   module). Replaces [Targetutils] (the register/sizes half) and
   [Calling_conventions] (the convention half).

   This is its OWN library (hike.abi, unwrapped) at the BOTTOM of the
   dependency lattice — both the vendored VSA libraries and the hike
   production library depend on it, so every register list, register
   predicate, and convention fact in the tree crosses this one module. *)

open Bap.Std
open Bap_core_theory
open Theory.Role.Register
open Bap.Std.Bil.Types

(* ------------------------------------------------------------------ *)
(* The convention record                                               *)
(* ------------------------------------------------------------------ *)

type t = {
  sp : var;                      (* the stack pointer *)
  fp : var;                      (* the frame pointer *)
  int_param_regs : var list;     (* the SysV integer/pointer arg registers *)
  vector_param_regs : var list;  (* the FP/vector arg registers (YMM0-7) *)
  return_regs : var list;        (* the integer return registers *)
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

(* Var-based predicates over the record ([Var.same] is base/name equality —
   a fresh RSP var matches the record's, and the fixpoint's env, keys). *)
let is_sp (t : t) (v : var) : bool = Var.same v t.sp
let is_fp (t : t) (v : var) : bool = Var.same v t.fp
let is_stack_reg (t : t) (v : var) : bool = is_sp t v || is_fp t v
let is_callee_saved (t : t) (v : var) : bool =
  Base.List.exists t.callee_saved ~f:(Var.same v)
let is_preserved (t : t) (v : var) : bool =
  is_stack_reg t v || is_callee_saved t v
(* the model-ABI structural lanes: the vector param registers (the
   phantom YMM args of the extern fallback signature) and the integer
   return registers (the RDX member of the {i64,i64} model return).
   A never-defined read of one of these is STRUCTURAL (the model ABI
   carries the whole register file), not an anomaly — the [hike:
   undef-read:] class aggregates them per-sub instead of warning each. *)
let is_vector_param_reg (t : t) (v : var) : bool =
  Base.List.exists t.vector_param_regs ~f:(Var.same v)
let is_return_reg (t : t) (v : var) : bool =
  Base.List.exists t.return_regs ~f:(Var.same v)

(* ------------------------------------------------------------------ *)
(* Target-derived registers and sizes (ex-Targetutils)                 *)
(* ------------------------------------------------------------------ *)

let addr_size_bits target =
  if Theory.Target.is_unknown target then 0
  else Theory.Target.data_addr_size target

let sp target =
  Base.Option.value_exn ~message:"set_sp: stack pointer not found"
    (Theory.Target.reg target stack_pointer)
  |> Var.reify

let fp target =
  Base.Option.value_exn ~message:"set_fp: frame pointer not found"
    (Theory.Target.reg target frame_pointer)
  |> Var.reify

let pc target =
  if Theory.Target.matches target "x86_64-gnu-elf" then
    Var.create "RIP" (Imm (Theory.Target.data_addr_size target))
  else failwith "pc: PC not defined for this target"

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

(* ------------------------------------------------------------------ *)
(* Target -> record, plus convenience accessors. This is the ONLY way  *)
(* a consumer outside this module touches a register list or predicate.*)
(* ------------------------------------------------------------------ *)

let imm width = Imm width
let r64 name = Var.create name (imm 64)
let r256 name = Var.create name (imm 256)

(* The one target this pipeline supports today; the record's vars are the
   TARGET-derived sp/fp (interchangeable with the vendored record's vars by
   NAME — [Var.same] is name-keyed). [of_target_opt] is TOTAL — None for a
   target this pipeline has no record for (the unit fixtures'
   [Theory.Target.unknown]); [of_target] is the checked accessor. *)
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
  match of_target_opt target with
  | Some t -> t
  | None -> failwith "abi not supported"

let int_param_regs target = (of_target target).int_param_regs
let vector_param_regs target = (of_target target).vector_param_regs
let param_regs target = param_regs (of_target target)
let return_regs target = (of_target target).return_regs
let callee_saved target = (of_target target).callee_saved

let is_sp_t target v = is_sp (of_target target) v
let is_fp_t target v = is_fp (of_target target) v
let is_sp_or_fp_t target v = is_stack_reg (of_target target) v
let is_callee_saved_t target v = is_callee_saved (of_target target) v

(* The FP-return detector's value-register names: the integer return
   registers plus their 32-bit views (the -O0 `return <double-expr>` shape
   leaves no RAX binding; the XMM0/YMM0 lane is [vector_param_regs]). *)
let value_return_names = [ "RAX"; "EAX"; "RDX"; "EDX" ]

(* The vector-register name prefix (the [is_ymm] tests). *)
let vector_param_prefix = "YMM"