open Bap.Std.Bil.Types
open Bap.Std
open Bap_core_theory
open Format
open Targetutils
module StrMap = Map.Make (String)

let subs : (Arg.t list * Arg.t list) StrMap.t ref = ref StrMap.empty

let get_calling_convention () =
  if Theory.Target.matches !target_ref "x86_64-gnu-elf" then
    Calling_conventions.x86_64_sysv
  else failwith "abi not supported"

let get_args sub_tid =
  match StrMap.find_opt (Tid.name sub_tid) !subs with
  | Some (_, args) -> args
  | None ->
      let callconv = get_calling_convention () in
      Base.List.map
        ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        callconv.param_regs

let get_rets sub_tid =
  match StrMap.find_opt (Tid.name sub_tid) !subs with
  | Some (rets, _) -> rets
  | None ->
      let callconv = get_calling_convention () in
      Base.List.map
        ~f:(fun reg -> Arg.create ~intent:Out reg (Var reg))
        callconv.return_regs

let var_size var =
  match Var.typ var with Imm n -> n | _ -> failwith "var size: non-imm var"

let goto_label_exn jmp =
  match jmp with Goto l -> l | _ -> failwith "goto_label_exn: ret jmp"

let is_void tid = get_rets tid = []

let label_tid label =
  match label with
  | Direct tid -> tid
  | Indirect _ -> failwith "label_tid: indirect label"

let label_exp label =
  match label with
  | Direct _ -> failwith "label_exp: direct label"
  | Indirect exp -> exp

type cf_type = Br | Ret | CallFun of Tid.t | Int | CallFunVoid | CallIndirect

let cf_type control_flow =
  let br = Seq.hd_exn control_flow in
  match Jmp.kind br with
  | Goto _ -> Br
  | Ret _ -> Ret
  | Call c -> (
      match Call.return c with
      | Some _ -> (
          match Call.target c with
          | Direct tid -> if is_void tid then CallFunVoid else CallFun tid
          | Indirect _ -> CallIndirect)
      | None -> Ret)
  | Int _ -> Int

let call_exn jmp =
  match Jmp.kind jmp with Call j -> j | _ -> failwith "call_exn:"

let base_exp_sub base_var sub =
  object
    inherit Exp.mapper
    method! map_var var = if Var.same var base_var then Var sub else Var var
  end

let get_bil_pass name =
  Base.List.find_exn ~f:(fun pass -> Bil.Pass.name pass = name) (Bil.passes ())

let get_pass name =
  Project.find_pass name
  |> Base.Option.value_exn ~message:("pass " ^ name ^ " not found")

let run_pass proj name =
  let pass = get_pass name in
  Project.Pass.run_exn pass proj

let sanitize_name =
  Base.String.filter ~f:(fun c ->
      if c = '#' then false
      else if c = '.' then false
      else if c = '%' then false
      else if c = '\\' then false
      else if c = '@' then false
      else true)

let bb_reg_name reg tid =
  sanitize_name @@ "reg_" ^ Var.name reg ^ "_" ^ Tid.name tid

let bb_phi_reg_name reg tid =
  sanitize_name @@ "phi_reg_" ^ Var.name reg ^ "_" ^ Tid.name tid

let bb_arg_name arg tid =
  sanitize_name @@ "arg" ^ Var.name arg ^ "_" ^ Tid.name tid

let bb_ret_name arg tid =
  sanitize_name @@ "ret_" ^ Var.name arg ^ "_" ^ Tid.name tid

let bb_var_name var tid = sanitize_name @@ Var.name var ^ "_" ^ Tid.name tid

let entry_blk_tid sub =
  let blks = Term.enum blk_t sub in
  Term.tid (Seq.hd_exn blks)

let create_var base ~typ ~tid =
  Var.create ~is_virtual:false (bb_var_name base tid) typ

let create_reg base ~typ ~tid =
  Var.create ~is_virtual:false (bb_reg_name base tid) typ

let create_arg base ~typ ~tid =
  Var.create ~is_virtual:false (bb_arg_name base tid) typ

let create_ret base ~typ ~tid =
  Var.create ~is_virtual:false (bb_ret_name base tid) typ

let create_phi_reg base ~typ ~tid =
  Var.create ~is_virtual:false (bb_phi_reg_name base tid) typ

let is_ret_reg rets var =
  Option.is_some
  @@ Base.List.find rets ~f:(fun ret -> Var.same (Arg.lhs ret) var)

let correct_registers sub_tid tid =
  let rets = get_rets sub_tid in
  object
    inherit Exp.mapper

    method! map_var var =
      if is_ret_reg rets var then Var (create_ret var ~tid ~typ:(Var.typ var))
      else if Base.List.mem !base_regs var ~equal:Var.same then
        Var (create_phi_reg var ~tid ~typ:(Var.typ var))
      else Var var
  end
