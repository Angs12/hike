open Bap.Std
open Bap_core_theory
open Theory.Role.Register
open Bap.Std.Bil.Types

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
