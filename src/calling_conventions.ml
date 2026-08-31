open Bap.Std
open Bap.Std.Bil.Types

type calling_convention = {
  name : string;
  return_regs : Var.t list;
  param_regs : Var.t list;
}

let imm width = Imm width

let r64 name = Var.create name (imm 64)
let r256 name = Var.create name (imm 256)

let x86_64_sysv : calling_convention = {
  name = "x86_64_sysv";
  return_regs = [r64 "RAX"; r64 "RDX"];
  param_regs =
    [r64 "RDI"; r64 "RSI"; r64 "RDX"; r64 "RCX"; r64 "R8"; r64 "R9"]
    @ Base.List.map ~f:(fun i -> r256 ("YMM" ^ Int.to_string i))
        (Base.List.range 0 8);
}

