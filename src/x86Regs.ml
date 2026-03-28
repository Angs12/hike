open Bap.Std
open Bap_core_theory
open Theory.Role.Register
open Bap.Std.Bil.Types

let ret_reg = ref @@ Var.create "DUMMY" (Imm 1)

let set_ret_reg target =
  Format.fprintf Format.err_formatter "Target :%a\n" Theory.Target.pp target;
  let reg =
    if Theory.Target.matches target "i686-gnu-elf" then
      Var.create "EAX" (Imm 32)
    else if Theory.Target.matches target "x86_64-gnu-elf" then
      Var.create "RAX" (Imm 64)
    else failwith "unsupported target"
  in
  Format.fprintf Format.err_formatter "ret_reg: %a\n" Var.pp reg;
  ret_reg := reg

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
let fp = ref @@ Var.create "DUMMY" (Imm 1)
let ptrsize = ref @@ 0
let base_regs = ref []
let set_ptrsize target = ptrsize := Theory.Target.bits target

let set_sp target =
  sp :=
    Base.Option.value_exn ~message:"set_sp: stack pointer not found"
      (Theory.Target.reg target stack_pointer)
    |> Var.reify

let set_fp target =
  fp :=
    Base.Option.value_exn ~message:"set_fp: frame pointer not found"
      (Theory.Target.reg target frame_pointer)
    |> Var.reify

let set_regs target =
  base_regs :=
    Theory.Target.regs target |> Base.Set.to_list |> Base.List.map ~f:Var.reify

let set_stack target =
  let byte = Theory.Target.byte target in
  let bits =
    match Theory.Target.bits target with
    | 32 -> `r32
    | 64 -> `r64
    | _ -> failwith "stack: non-32 or 64 bits"
  in
  stack := Var.create "stack" (Mem (bits, Size.of_int_exn byte))

let resolve_alias target reg =
  let sort = Var.sort reg in
  let name = Var.name reg in
  let theory_var = Theory.Var.define sort name in
  Option.bind (Theory.Target.unalias target theory_var) Theory.Origin.cast_sub

let theory_regs target = Theory.Target.regs target |> Base.Set.to_list

let basis_regs target =
  let all_theory_regs = theory_regs target in
  let is_basis reg =
    match Theory.Target.unalias target reg with None -> true | Some _ -> false
  in
  let basis_theory_regs = List.filter is_basis all_theory_regs in
  List.map (fun r -> Var.reify r) basis_theory_regs

let set_base_regs target = base_regs := basis_regs target
