open Bap.Std
open Bap_core_theory
open Theory.Role.Register
open Bap.Std.Bil.Types

let target_ref = ref Theory.Target.unknown
let ptrsize = ref 0

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
    Var.create "RIP" (Imm 64)
  else failwith "pc: PC not defined for this target"

let set_target_ref target = target_ref := target
let set_ptrsize size = ptrsize := Theory.Target.bits size

let resolve_alias target reg =
  let sort = Var.sort reg in
  let name = Var.name reg in
  let theory_var = Theory.Var.define sort name in
  Option.bind (Theory.Target.unalias target theory_var) Theory.Origin.cast_sub

let theory_regs target = Theory.Target.regs target |> Base.Set.to_list

let base_regs target =
  let all_theory_regs = theory_regs target in
  let is_basis reg =
    match Theory.Target.unalias target reg with None -> true | Some _ -> false
  in
  let basis_theory_regs = List.filter is_basis all_theory_regs in
  Base.List.map ~f:Var.reify basis_theory_regs
