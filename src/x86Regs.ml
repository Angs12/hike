open Bap.Std
open Bap_core_theory
open Theory.Role.Register
open Bap.Std.Bil.Types
open Format

let ret_reg = ref @@ Var.create "DUMMY" (Imm 1)

let set_ret_reg target =
  let abi = Theory.Target.abi target in
  if abi = Theory.Abi.gnu then ret_reg := Var.create "RAX" (Imm 64)
  else failwith "unsupported target"

let cpu_regs = Var.create "cpu" (Mem (`r32, Size.of_int_exn 8))
let mem = ref @@ Var.create "DUMMY" (Mem (`r32, Size.of_int_exn 8))

let set_mem target =
  let byte = Theory.Target.byte target in
  let bits =
    match Theory.Target.bits target with
    | 32 -> `r32
    | 64 -> `r64
    | _ -> failwith "mem: non-32 or 64 bits"
  in
  mem := Var.create "mem" (Mem (bits, Size.of_int_exn byte))

let stack = ref @@ Var.create "DUMMY" (Mem (`r32, Size.of_int_exn 8))
let sp = ref @@ Var.create "DUMMY" (Imm 1)
let regs = ref []

let set_sp target =
  sp :=
    Base.Option.value_exn ~message:"set_sp: stack pointer not found"
      (Theory.Target.reg target stack_pointer)
    |> Var.reify

let set_regs target =
  let flags =
    [
      Var.create "CF" (Imm 1);
      Var.create "PF" (Imm 1);
      Var.create "AF" (Imm 1);
      Var.create "ZF" (Imm 1);
      Var.create "SF" (Imm 1);
      Var.create "TF" (Imm 1);
      Var.create "IF" (Imm 1);
      Var.create "DF" (Imm 1);
      Var.create "OF" (Imm 1);
      Var.create "PF" (Imm 1);
    ]
  in
  regs :=
    Theory.Target.regs target |> Base.Set.to_list |> Base.List.map ~f:Var.reify
    |> Base.List.filter ~f:(fun reg ->
        not (Base.List.mem flags reg ~equal:Var.same))

let set_stack target =
  let byte = Theory.Target.byte target in
  let bits =
    match Theory.Target.bits target with
    | 32 -> `r32
    | 64 -> `r64
    | _ -> failwith "stack: non-32 or 64 bits"
  in
  stack := Var.create "stack" (Mem (bits, Size.of_int_exn byte))

let word_exp n = Bil.Int (Word.of_int ~width:32 n)

let get_reg reg =
  if Var.name reg = "CS" then
    Load (Var cpu_regs, word_exp 0, BigEndian, Size.r16)
  else if Var.name reg = "DS" then
    Load (Var cpu_regs, word_exp 2, BigEndian, Size.r16)
  else if Var.name reg = "ES" then
    Load (Var cpu_regs, word_exp 4, BigEndian, Size.r16)
  else if Var.name reg = "R10" then
    Load (Var cpu_regs, word_exp 6, BigEndian, Size.r64)
  else if Var.name reg = "R11" then
    Load (Var cpu_regs, word_exp 14, BigEndian, Size.r64)
  else if Var.name reg = "R12" then
    Load (Var cpu_regs, word_exp 22, BigEndian, Size.r64)
  else if Var.name reg = "R13" then
    Load (Var cpu_regs, word_exp 30, BigEndian, Size.r64)
  else if Var.name reg = "R14" then
    Load (Var cpu_regs, word_exp 38, BigEndian, Size.r64)
  else if Var.name reg = "R15" then
    Load (Var cpu_regs, word_exp 46, BigEndian, Size.r64)
  else if Var.name reg = "R8" then
    Load (Var cpu_regs, word_exp 54, BigEndian, Size.r64)
  else if Var.name reg = "R9" then
    Load (Var cpu_regs, word_exp 62, BigEndian, Size.r64)
  else if Var.name reg = "RAX" then
    Load (Var cpu_regs, word_exp 70, BigEndian, Size.r64)
  else if Var.name reg = "EAX" then
    Load (Var cpu_regs, word_exp 74, BigEndian, Size.r32)
  else if Var.name reg = "AX" then
    Load (Var cpu_regs, word_exp 76, BigEndian, Size.r16)
  else if Var.name reg = "RBP" then
    Load (Var cpu_regs, word_exp 78, BigEndian, Size.r64)
  else if Var.name reg = "EBP" then
    Load (Var cpu_regs, word_exp 82, BigEndian, Size.r32)
  else if Var.name reg = "BP" then
    Load (Var cpu_regs, word_exp 84, BigEndian, Size.r16)
  else if Var.name reg = "RBX" then
    Load (Var cpu_regs, word_exp 86, BigEndian, Size.r64)
  else if Var.name reg = "EBX" then
    Load (Var cpu_regs, word_exp 90, BigEndian, Size.r32)
  else if Var.name reg = "BX" then
    Load (Var cpu_regs, word_exp 92, BigEndian, Size.r16)
  else if Var.name reg = "RCX" then
    Load (Var cpu_regs, word_exp 94, BigEndian, Size.r64)
  else if Var.name reg = "ECX" then
    Load (Var cpu_regs, word_exp 98, BigEndian, Size.r32)
  else if Var.name reg = "CX" then
    Load (Var cpu_regs, word_exp 100, BigEndian, Size.r16)
  else if Var.name reg = "RDI" then
    Load (Var cpu_regs, word_exp 102, BigEndian, Size.r64)
  else if Var.name reg = "EDI" then
    Load (Var cpu_regs, word_exp 106, BigEndian, Size.r32)
  else if Var.name reg = "DI" then
    Load (Var cpu_regs, word_exp 108, BigEndian, Size.r16)
  else if Var.name reg = "RDX" then
    Load (Var cpu_regs, word_exp 110, BigEndian, Size.r64)
  else if Var.name reg = "EDX" then
    Load (Var cpu_regs, word_exp 114, BigEndian, Size.r32)
  else if Var.name reg = "DX" then
    Load (Var cpu_regs, word_exp 116, BigEndian, Size.r16)
  else if Var.name reg = "RSI" then
    Load (Var cpu_regs, word_exp 118, BigEndian, Size.r64)
  else if Var.name reg = "ESI" then
    Load (Var cpu_regs, word_exp 122, BigEndian, Size.r32)
  else if Var.name reg = "SI" then
    Load (Var cpu_regs, word_exp 124, BigEndian, Size.r16)
  else if Var.name reg = "RSP" then
    Load (Var cpu_regs, word_exp 126, BigEndian, Size.r64)
  else if Var.name reg = "ESP" then
    Load (Var cpu_regs, word_exp 130, BigEndian, Size.r32)
  else if Var.name reg = "SP" then
    Load (Var cpu_regs, word_exp 132, BigEndian, Size.r16)
  else if Var.name reg = "SS" then
    Load (Var cpu_regs, word_exp 134, BigEndian, Size.r16)
  else if Var.name reg = "YMM0" then
    Load (Var cpu_regs, word_exp 136, BigEndian, Size.r256)
  else if Var.name reg = "YMM1" then
    Load (Var cpu_regs, word_exp 168, BigEndian, Size.r256)
  else if Var.name reg = "YMM2" then
    Load (Var cpu_regs, word_exp 200, BigEndian, Size.r256)
  else if Var.name reg = "YMM3" then
    Load (Var cpu_regs, word_exp 232, BigEndian, Size.r256)
  else if Var.name reg = "YMM4" then
    Load (Var cpu_regs, word_exp 264, BigEndian, Size.r256)
  else if Var.name reg = "YMM5" then
    Load (Var cpu_regs, word_exp 296, BigEndian, Size.r256)
  else if Var.name reg = "YMM6" then
    Load (Var cpu_regs, word_exp 328, BigEndian, Size.r256)
  else if Var.name reg = "YMM7" then
    Load (Var cpu_regs, word_exp 360, BigEndian, Size.r256)
  else if Var.name reg = "YMM8" then
    Load (Var cpu_regs, word_exp 392, BigEndian, Size.r256)
  else if Var.name reg = "YMM9" then
    Load (Var cpu_regs, word_exp 424, BigEndian, Size.r256)
  else if Var.name reg = "YMM10" then
    Load (Var cpu_regs, word_exp 456, BigEndian, Size.r256)
  else if Var.name reg = "YMM11" then
    Load (Var cpu_regs, word_exp 488, BigEndian, Size.r256)
  else if Var.name reg = "YMM12" then
    Load (Var cpu_regs, word_exp 520, BigEndian, Size.r256)
  else if Var.name reg = "YMM13" then
    Load (Var cpu_regs, word_exp 552, BigEndian, Size.r256)
  else if Var.name reg = "YMM14" then
    Load (Var cpu_regs, word_exp 584, BigEndian, Size.r256)
  else if Var.name reg = "YMM15" then
    Load (Var cpu_regs, word_exp 616, BigEndian, Size.r256)
  else (
    fprintf err_formatter "get_reg: not implemented %s\n" (Var.name reg);
    failwith "get_reg: not implemented")

let set_reg reg data =
  if Var.name reg = "CS" then
    Store (Var cpu_regs, word_exp 0, data, BigEndian, Size.r16)
  else if Var.name reg = "DS" then
    Store (Var cpu_regs, word_exp 2, data, BigEndian, Size.r16)
  else if Var.name reg = "ES" then
    Store (Var cpu_regs, word_exp 4, data, BigEndian, Size.r16)
  else if Var.name reg = "R10" then
    Store (Var cpu_regs, word_exp 6, data, BigEndian, Size.r64)
  else if Var.name reg = "R11" then
    Store (Var cpu_regs, word_exp 14, data, BigEndian, Size.r64)
  else if Var.name reg = "R12" then
    Store (Var cpu_regs, word_exp 22, data, BigEndian, Size.r64)
  else if Var.name reg = "R13" then
    Store (Var cpu_regs, word_exp 30, data, BigEndian, Size.r64)
  else if Var.name reg = "R14" then
    Store (Var cpu_regs, word_exp 38, data, BigEndian, Size.r64)
  else if Var.name reg = "R15" then
    Store (Var cpu_regs, word_exp 46, data, BigEndian, Size.r64)
  else if Var.name reg = "R8" then
    Store (Var cpu_regs, word_exp 54, data, BigEndian, Size.r64)
  else if Var.name reg = "R9" then
    Store (Var cpu_regs, word_exp 62, data, BigEndian, Size.r64)
  else if Var.name reg = "RAX" then
    Store (Var cpu_regs, word_exp 70, data, BigEndian, Size.r64)
  else if Var.name reg = "RBP" then
    Store (Var cpu_regs, word_exp 78, data, BigEndian, Size.r64)
  else if Var.name reg = "RBX" then
    Store (Var cpu_regs, word_exp 86, data, BigEndian, Size.r64)
  else if Var.name reg = "RCX" then
    Store (Var cpu_regs, word_exp 94, data, BigEndian, Size.r64)
  else if Var.name reg = "RDI" then
    Store (Var cpu_regs, word_exp 102, data, BigEndian, Size.r64)
  else if Var.name reg = "RDX" then
    Store (Var cpu_regs, word_exp 110, data, BigEndian, Size.r64)
  else if Var.name reg = "RSI" then
    Store (Var cpu_regs, word_exp 118, data, BigEndian, Size.r64)
  else if Var.name reg = "RSP" then
    Store (Var cpu_regs, word_exp 126, data, BigEndian, Size.r64)
  else if Var.name reg = "SS" then
    Store (Var cpu_regs, word_exp 134, data, BigEndian, Size.r16)
  else if Var.name reg = "YMM0" then
    Store (Var cpu_regs, word_exp 136, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM1" then
    Store (Var cpu_regs, word_exp 168, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM2" then
    Store (Var cpu_regs, word_exp 200, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM3" then
    Store (Var cpu_regs, word_exp 232, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM4" then
    Store (Var cpu_regs, word_exp 264, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM5" then
    Store (Var cpu_regs, word_exp 296, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM6" then
    Store (Var cpu_regs, word_exp 328, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM7" then
    Store (Var cpu_regs, word_exp 360, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM8" then
    Store (Var cpu_regs, word_exp 392, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM9" then
    Store (Var cpu_regs, word_exp 424, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM10" then
    Store (Var cpu_regs, word_exp 456, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM11" then
    Store (Var cpu_regs, word_exp 488, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM12" then
    Store (Var cpu_regs, word_exp 520, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM13" then
    Store (Var cpu_regs, word_exp 552, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM14" then
    Store (Var cpu_regs, word_exp 584, data, BigEndian, Size.r256)
  else if Var.name reg = "YMM15" then
    Store (Var cpu_regs, word_exp 616, data, BigEndian, Size.r256)
  else failwith "set_reg: not implemented"
