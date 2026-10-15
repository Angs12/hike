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
  return_regs : var list;        (* return registers, integer and vector *)
  callee_saved : var list;       (* callee-saved GPRs (incl. RBP) *)
  caller_saved_gprs : var list;  (* GPRs a call may clobber (SysV) *)
  variadic_count_reg : var option; (* the lane carrying the vector-register
                                      count at a variadic call (SysV: RAX) *)
  env_regs : var list;           (* process-global environment registers
                                    (the x87 control word, MXCSR): never
                                    call-crossing, persistent per process *)
  flag_regs : var list;          (* the arithmetic flags: call-clobbered,
                                    undefined at sub entry *)
  word : int;                    (* target word size in bytes *)
  page_size : int64;             (* the runtime page: the loader's RELRO
                                    mprotect rounds to it *)
  entry_symbol : string;         (* the process entry's linker symbol, the
                                    runtime boundary a dead continuation
                                    binds to (SysV: _start) *)
  noreturn_symbols : string list; (* the runtime contract's never-returning
                                    functions (the base fact for body-less
                                    externs; DWARF extends it upstream) *)
}

let x86_64_sysv : t =
  let r64 name = Var.create ~is_virtual:false ~fresh:false name (Type.Imm 64) in
  let r256 name = Var.create ~is_virtual:false ~fresh:false name (Type.Imm 256) in
  let rax = r64 "RAX" in
  {
    sp = r64 "RSP";
    thread_pointer = r64 "FS_BASE";
    int_param_regs =
      Base.List.map ~f:r64 [ "RDI"; "RSI"; "RDX"; "RCX"; "R8"; "R9" ];
    vector_param_regs =
      Base.List.map ~f:r256
        (Base.List.map ~f:(fun i -> "YMM" ^ Base.Int.to_string i)
           (Base.List.range 0 8));
    return_regs = [ rax; r64 "RDX"; r256 "YMM0" ];
    callee_saved = Base.List.map ~f:r64 [ "RBX"; "RBP"; "R12"; "R13"; "R14"; "R15" ];
    caller_saved_gprs =
      Base.List.map ~f:r64
        [ "RAX"; "RCX"; "RDX"; "RSI"; "RDI"; "R8"; "R9"; "R10"; "R11" ];
    variadic_count_reg = Some rax;
    env_regs =
      [ Var.create ~is_virtual:false ~fresh:false "FPU_CONTROL" (Type.Imm 16);
        Var.create ~is_virtual:false ~fresh:false "MXCSR" (Type.Imm 32) ];
    flag_regs =
      Base.List.map
        ~f:(fun name ->
          Var.create ~is_virtual:false ~fresh:false name (Type.Imm 1))
        [ "CF"; "PF"; "AF"; "ZF"; "SF"; "OF" ];
    word = 8;
    page_size = 4096L;
    entry_symbol = "_start";
    noreturn_symbols =
      [ "longjmp"; "siglongjmp"; "__stack_chk_fail"; "abort"; "exit";
        "_exit"; "_Exit"; "quick_exit"; "__assert_fail"; "pthread_exit";
        "__libc_start_main" ];
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
let is_env_reg (t : t) (v : var) : bool =
  Base.List.exists t.env_regs ~f:(Var.same v)
let is_flag_reg (t : t) (v : var) : bool =
  Base.List.exists t.flag_regs ~f:(Var.same v)

(* BAP spells mapped targets [@name]; the leading [@] is a display prefix,
   not part of the name. *)
let strip_at (name : string) : string =
  if String.length name > 0 && name.[0] = '@' then
    String.sub name 1 (String.length name - 1)
  else name

(* BAP names mapped intrinsic targets [@intrinsic:<name>]. *)
let is_intrinsic_name (name : string) : bool =
  Base.String.is_prefix (strip_at name) ~prefix:"intrinsic:"

let is_intrinsic_target (t : tid) : bool =
  is_intrinsic_name (Tid.name t)

(* The atomic-family intrinsics the x86 backend emits: the lock-marker
   pair bracketing every locked memory RMW (a memory xchg's is
   implicit), and the three fences.  They are facts about one
   instruction, not code: no machine convention rides them. *)
let is_lock_marker (name : string) : bool =
  match strip_at name with
  | "intrinsic:x86:lock" | "intrinsic:x86:unlock" -> true
  | _ -> false

let is_fence_intrinsic (name : string) : bool =
  match strip_at name with
  | "intrinsic:mfence" | "intrinsic:lfence" | "intrinsic:sfence" -> true
  | _ -> false

let is_atomic_intrinsic_name (name : string) : bool =
  is_lock_marker name || is_fence_intrinsic name

(* The trap-id vocabulary's one test (the divide-by-zero interrupt sub). *)
let is_interrupt_name (n : string) : bool =
  Base.String.is_prefix n ~prefix:"@interrupt:"

(* Argument registers in convention order: integer, then vector. *)
let param_regs (t : t) : var list = t.int_param_regs @ t.vector_param_regs

let addr_size_bits target =
  if Theory.Target.is_unknown target then 0
  else Theory.Target.data_addr_size target

(* The machine size word for [bits]-bit addresses. *)
let addr_size_of_bits (bits : int) : [> `r32 | `r64 ] =
  if bits <= 32 then `r32 else `r64

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

(* A recognized target that is not the primary one: the pass entry warns
   that the x86-64 convention record serves it. *)
let is_known_foreign (t : Theory.Target.t) : bool =
  not (Theory.Target.is_unknown t) && not (is_primary_target t)

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
      variadic_count_reg = x86_64_sysv.variadic_count_reg;
      env_regs = x86_64_sysv.env_regs;
      flag_regs = x86_64_sysv.flag_regs;
      word = Theory.Target.bits target / 8;
      page_size = x86_64_sysv.page_size;
      entry_symbol = x86_64_sysv.entry_symbol;
      noreturn_symbols = x86_64_sysv.noreturn_symbols;
    }
  else x86_64_sysv

(* The target's word size in bits, from the byte size the record carries. *)
let word_bits (t : t) : int = 8 * t.word

(* SysV stack alignment: every stack object is 16-byte aligned. *)
let stack_align = 16

(* The convention's named lanes: the FP return rides the first vector
   register; the fixed (argc, argv) signature reads the first two
   integer params. *)
let argc_argv_regs (t : t) : var * var =
  match t.int_param_regs with
  | rdi :: rsi :: _ -> (rdi, rsi)
  | _ -> failwith "hike_abi: fewer than two integer param registers"

