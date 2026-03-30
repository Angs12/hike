open Bap.Std
open Bap.Std.Bil.Types

type calling_convention = {
  name : string;
  return_regs : Var.t list;
  param_regs : Var.t list;
}

let imm width = Imm width

let r64 name = Var.create name (imm 64)
let r32 name = Var.create name (imm 32)
let r128 name = Var.create name (imm 128)

let x86_64_sysv : calling_convention = {
  name = "x86_64_sysv";
  return_regs = [r64 "RAX"; r64 "RDX"];
  param_regs = [r64 "RDI"; r64 "RSI"; r64 "RDX"; r64 "RCX"; r64 "R8"; r64 "R9"];
}

let x86_64_ms : calling_convention = {
  name = "x86_64_ms";
  return_regs = [r64 "RAX"; r64 "RDX"];
  param_regs = [r64 "RCX"; r64 "RDX"; r64 "R8"; r64 "R9"];
}

let x86_cdecl : calling_convention = {
  name = "x86_cdecl";
  return_regs = [r32 "EAX"];
  param_regs = [];
}

let x86_stdcall : calling_convention = {
  name = "x86_stdcall";
  return_regs = [r32 "EAX"];
  param_regs = [];
}

let x86_fastcall : calling_convention = {
  name = "x86_fastcall";
  return_regs = [r32 "EAX"; r32 "EDX"];
  param_regs = [r32 "ECX"; r32 "EDX"];
}

let x86_thiscall : calling_convention = {
  name = "x86_thiscall";
  return_regs = [r32 "EAX"];
  param_regs = [r32 "ECX"];
}

let arm64_aapcs : calling_convention = {
  name = "arm64_aapcs";
  return_regs = [r64 "X0"; r64 "X1"; r128 "V0"; r128 "V1"];
  param_regs = [
    r64 "X0"; r64 "X1"; r64 "X2"; r64 "X3";
    r64 "X4"; r64 "X5"; r64 "X6"; r64 "X7";
    r128 "V0"; r128 "V1"; r128 "V2"; r128 "V3";
    r128 "V4"; r128 "V5"; r128 "V6"; r128 "V7";
  ];
}

let arm32_aapcs : calling_convention = {
  name = "arm32_aapcs";
  return_regs = [r32 "R0"; r128 "S0"];
  param_regs = [
    r32 "R0"; r32 "R1"; r32 "R2"; r32 "R3";
    r128 "S0"; r128 "S1"; r128 "S2"; r128 "S3";
  ];
}

let mips_o32 : calling_convention = {
  name = "mips_o32";
  return_regs = [r32 "$2"; r32 "$3"];
  param_regs = [r32 "$4"; r32 "$5"; r32 "$6"; r32 "$7"];
}

let mips_n64 : calling_convention = {
  name = "mips_n64";
  return_regs = [r64 "$2"; r64 "$3"];
  param_regs = [
    r64 "$4"; r64 "$5"; r64 "$6"; r64 "$7";
    r64 "$8"; r64 "$9"; r64 "$10"; r64 "$11";
  ];
}

let ppc32 : calling_convention = {
  name = "ppc32";
  return_regs = [r32 "r3"];
  param_regs = [
    r32 "r3"; r32 "r4"; r32 "r5"; r32 "r6";
    r32 "r7"; r32 "r8"; r32 "r9"; r32 "r10";
  ];
}

let ppc64 : calling_convention = {
  name = "ppc64";
  return_regs = [r64 "r3"];
  param_regs = [
    r64 "r3"; r64 "r4"; r64 "r5"; r64 "r6";
    r64 "r7"; r64 "r8"; r64 "r9"; r64 "r10";
  ];
}

let riscv_rv64 : calling_convention = {
  name = "riscv_rv64";
  return_regs = [r64 "a0"; r64 "a1"; r128 "fa0"; r128 "fa1"];
  param_regs = [
    r64 "a0"; r64 "a1"; r64 "a2"; r64 "a3";
    r64 "a4"; r64 "a5"; r64 "a6"; r64 "a7";
    r128 "fa0"; r128 "fa1"; r128 "fa2"; r128 "fa3";
    r128 "fa4"; r128 "fa5"; r128 "fa6"; r128 "fa7";
  ];
}

let riscv_rv32 : calling_convention = {
  name = "riscv_rv32";
  return_regs = [r32 "a0"; r32 "a1"; r128 "fa0"; r128 "fa1"];
  param_regs = [
    r32 "a0"; r32 "a1"; r32 "a2"; r32 "a3";
    r32 "a4"; r32 "a5"; r32 "a6"; r32 "a7";
    r128 "fa0"; r128 "fa1"; r128 "fa2"; r128 "fa3";
    r128 "fa4"; r128 "fa5"; r128 "fa6"; r128 "fa7";
  ];
}

let all : calling_convention list = [
  x86_64_sysv;
  x86_64_ms;
  x86_cdecl;
  x86_stdcall;
  x86_fastcall;
  x86_thiscall;
  arm64_aapcs;
  arm32_aapcs;
  mips_o32;
  mips_n64;
  ppc32;
  ppc64;
  riscv_rv64;
  riscv_rv32;
]

let find_by_name name =
  List.find_opt (fun cc -> cc.name = name) all

let return_regs name =
  match find_by_name name with
  | Some cc -> cc.return_regs
  | None -> []

let param_regs name =
  match find_by_name name with
  | Some cc -> cc.param_regs
  | None -> []
