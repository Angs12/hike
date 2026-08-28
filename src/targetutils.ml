open Bap.Std
open Bap_core_theory
open Theory.Role.Register
open Bap.Std.Bil.Types

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
