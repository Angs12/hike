open Bap.Std.Bil.Types
open Bap.Std
open Bap_core_theory
open Targetutils
module StrMap = Map.Make (String)

type llvalue_map = Llvm.llvalue StrMap.t
type blk_llvals = { phis : llvalue_map ref; regs : llvalue_map ref }

let sub_llvars : llvalue_map ref = ref StrMap.empty
let blk_llvals : blk_llvals Tid.Map.t ref = ref Tid.Map.empty
let subs : (Arg.t list * Arg.t list) Tid.Map.t ref = ref Tid.Map.empty

let insert_sub_sig tid ~rets ~args =
  subs := Tid.Map.add_exn !subs ~key:tid ~data:(rets, args)

let get_calling_convention () =
  if Theory.Target.matches !target_ref "x86_64-gnu-elf" then
    Calling_conventions.x86_64_sysv
  else failwith "abi not supported"

let typ_lltype llvm_ctx typ =
  match typ with
  | Imm n -> Llvm.integer_type llvm_ctx n
  | _ -> Llvm.pointer_type llvm_ctx

let get_direct_call jmp =
  match Jmp.kind jmp with
  | Call c -> (
      match Call.target c with Direct target -> Some target | _ -> None)
  | _ -> None

let get_args sub_tid =
  match Tid.Map.find !subs sub_tid with
  | Some (_, args) -> args
  | None ->
      let callconv = get_calling_convention () in
      Base.List.map
        ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
        callconv.param_regs

let get_rets sub_tid =
  match Tid.Map.find !subs sub_tid with
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

(* Stub for now *)
let is_void _ = false

let label_tid label =
  match label with
  | Direct tid -> tid
  | Indirect _ -> failwith "label_tid: indirect label"

let label_exp label =
  match label with
  | Direct _ -> failwith "label_exp: direct label"
  | Indirect exp -> exp

let sanitize_name =
  Base.String.filter ~f:(fun c ->
      if c = '#' then false
      else if c = '.' then false
      else if c = '%' then false
      else if c = '\\' then false
      else if c = '@' then false
      else true)

type cf_type = Br | Ret | CallFun | Int | CallFunVoid | CallIndirect

let clear_sub_llvars () = sub_llvars := StrMap.empty
let clear_blk_llvars () = blk_llvals := Tid.Map.empty

let insert_llval_name name value =
  sub_llvars := StrMap.add (sanitize_name name) value !sub_llvars

let insert_var var value =
  sub_llvars := StrMap.add (sanitize_name @@ Var.name var) value !sub_llvars

let init_blk_llvals blk_tid =
  let phis = ref StrMap.empty in
  let regs = ref StrMap.empty in
  blk_llvals := Tid.Map.add_exn !blk_llvals ~key:blk_tid ~data:{ phis; regs }

let insert_phi blk_tid var value =
  let blk_llvals = Tid.Map.find_exn !blk_llvals blk_tid in
  blk_llvals.phis :=
    StrMap.add (sanitize_name @@ Var.name var) value !(blk_llvals.phis)

let insert_phi_reg blk_tid var value =
  let blk_llvals = Tid.Map.find_exn !blk_llvals blk_tid in
  blk_llvals.regs :=
    StrMap.add (sanitize_name @@ Var.name var) value !(blk_llvals.regs)

let get_phi_reg blk_tid var =
  let blk_llvals = Tid.Map.find_exn !blk_llvals blk_tid in
  match StrMap.find_opt (sanitize_name @@ Var.name var) !(blk_llvals.regs) with
  | Some v -> v
  | None ->
      failwith @@ "Phi reg "
      ^ (sanitize_name @@ Var.name var)
      ^ " not found at blk " ^ Tid.name blk_tid

let get_phi blk_tid var =
  let blk_llvals = Tid.Map.find_exn !blk_llvals blk_tid in
  match StrMap.find_opt (sanitize_name @@ Var.name var) !(blk_llvals.phis) with
  | Some v -> v
  | None ->
      failwith @@ "Phi "
      ^ (sanitize_name @@ Var.name var)
      ^ " not found at blk " ^ Tid.name blk_tid

let get_llval var =
  let name = sanitize_name @@ Var.name var in
  match StrMap.find_opt name !sub_llvars with
  | Some v -> v
  | None -> failwith @@ "Variable " ^ name ^ " not found"

let is_goto jmp = match Jmp.kind jmp with Goto _ -> true | _ -> false

let cf_type control_flow =
  let br = Seq.hd_exn control_flow in
  match Jmp.kind br with
  | Goto _ -> Br
  | Ret _ -> Ret
  | Call c -> (
      match Call.return c with
      | Some _ -> (
          match Call.target c with
          | Direct tid -> if is_void tid then CallFunVoid else CallFun
          | Indirect _ -> CallIndirect)
      | None -> (
          match Call.target c with Indirect _ -> Ret | Direct _ -> CallFun))
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

let bb_reg_name reg tid =
  sanitize_name @@ "reg_" ^ Var.name reg ^ "_" ^ Tid.name tid

let bb_phi_reg_name reg tid =
  sanitize_name @@ "phi_reg_" ^ Var.name reg ^ "_" ^ Tid.name tid

let entry_blk_tid sub =
  let cfg = Sub.to_graph sub in
  Graphs.Tid.Node.succs Graphs.Tid.start cfg |> Seq.hd_exn

let create_reg base ~typ ~tid =
  Var.create ~is_virtual:false (bb_reg_name base tid) typ

let create_phi_reg base ~typ ~tid =
  Var.create ~is_virtual:false (bb_phi_reg_name base tid) typ
