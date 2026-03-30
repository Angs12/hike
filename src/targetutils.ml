open Bap.Std
open Bap_core_theory
open Theory.Role.Register
open Bap.Std.Bil.Types

let stack = ref @@ Var.create "DUMMY" (Mem (`r32, Size.of_int_exn 8))
let sp = ref @@ Var.create "DUMMY" (Imm 1)
let fp = ref @@ Var.create "DUMMY" (Imm 1)
let base_regs = ref []
let target_ref = ref Theory.Target.unknown
let ptrsize = ref 0
let set_target_ref target = target_ref := target
let set_ptrsize size = ptrsize := Theory.Target.bits size

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
  Base.List.map ~f:Var.reify basis_theory_regs

let set_base_regs target = base_regs := basis_regs target
