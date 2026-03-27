open Bap.Std
open X86Regs
open Bap_main
open Bap.Std.Bil.Types
open Regular.Std
open Reachable_funcs
open Bap_core_theory
open Bap_main.Extension.Command
open Format
module StrMap = Map.Make (String)
module ExpMap = Map.Make (Exp)
module KB = Bap_knowledge.Knowledge

let subs = ref StrMap.empty

let get_args sub_tid =
  snd
  @@ Base.Option.value_exn
       ~message:(sprintf "get_args : sub %s not found" (Tid.name sub_tid))
       (StrMap.find_opt (Tid.name sub_tid) !subs)

let get_rets sub_tid =
  fst
  @@ Base.Option.value_exn
       ~message:(sprintf "get_rets : sub %s not found" (Tid.name sub_tid))
       (StrMap.find_opt (Tid.name sub_tid) !subs)

let get_section_mem name proj =
  let mem, _ =
    Project.memory proj |> Memmap.to_sequence
    |> Seq.find_exn ~f:(fun (_, v) ->
        Base.Option.value_map (Value.get Image.section v) ~default:false
          ~f:(fun n -> String.equal n name))
  in
  mem

let get_section name proj =
  let mem, _ =
    Project.memory proj |> Memmap.to_sequence
    |> Seq.find_exn ~f:(fun (_, v) ->
        Base.Option.value_map (Value.get Image.section v) ~default:false
          ~f:(fun n -> String.equal n name))
  in
  let lenght = Memory.length mem in
  let min_addr = Memory.min_addr mem in
  let arr = Base.Array.init lenght ~f:(fun _ -> 0) in
  Memory.iteri ~word_size:`r8 mem ~f:(fun index v ->
      arr.(Word.to_int_exn (Word.( - ) index min_addr)) <- Word.to_int_exn v);
  arr

let print_sections p =
  Project.memory p |> Memmap.to_sequence
  |> Seq.iter ~f:(fun (mem, x) ->
      Base.Option.iter (Value.get Image.section x) ~f:(fun name ->
          eprintf "Section: %s@.%a@." name Memory.pp mem))

let is_mem var = match Var.typ var with Mem _ -> true | _ -> false

let var_size var =
  match Var.typ var with Imm n -> n | _ -> failwith "var size: non-imm var"

let free_vars sub =
  Sub.free_vars sub
  |> Var.Set.filter ~f:(fun var -> not @@ is_mem var)
  |> Var.Set.filter ~f:(fun var -> not @@ Var.same var !ret_reg)
  |> Var.Set.to_list

let sanitize_name =
  Base.String.filter ~f:(fun c ->
      if c = '#' then false
      else if c = '.' then false
      else if c = '%' then false
      else if c = '\\' then false
      else if c = '\\' then false
      else if c = '@' then false
      else true)

let var_lltype llvm_ctx var =
  match Var.typ var with
  | Imm n -> Llvm.integer_type llvm_ctx n
  | _ -> failwith "var_lltype : non-imm var"

let bb_reg_name reg tid =
  sanitize_name @@ "reg_" ^ Var.name reg ^ "_" ^ Tid.name tid

let bb_phi_reg_name reg tid =
  sanitize_name @@ "phi_reg_" ^ Var.name reg ^ "_" ^ Tid.name tid

let bb_arg_name arg tid =
  sanitize_name @@ "arg" ^ Var.name arg ^ "_" ^ Tid.name tid

let bb_ret_name arg tid =
  sanitize_name @@ "ret_" ^ Var.name arg ^ "_" ^ Tid.name tid

let bb_var_name var tid = sanitize_name @@ Var.name var ^ "_" ^ Tid.name tid

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

let create_ret_type llvm_ctx = Llvm.integer_type llvm_ctx (var_size !ret_reg)
let sub_llvars = ref @@ StrMap.empty
let ll_funcs = ref @@ StrMap.empty
let llvar_from_name name = StrMap.find name !sub_llvars

let create_arg_types llvm_ctx sub_tid =
  let args = get_args sub_tid in
  Base.List.to_array args
  |> Base.Array.map ~f:(fun arg ->
      let var = Arg.lhs arg in
      var_lltype llvm_ctx var)

let set_arg_names fn sub_tid =
  let args = get_args sub_tid in
  Base.List.iteri args ~f:(fun i arg ->
      let param = Llvm.param fn i in
      Llvm.set_value_name (bb_arg_name (Arg.lhs arg) sub_tid) param)

let add_args_to_vars fn =
  Llvm.iter_params
    (fun param ->
      let name = Llvm.value_name param in
      sub_llvars := StrMap.add name param !sub_llvars)
    fn

let add_regs_to_vars llvm_ctx blk_tid =
  Base.List.iter !regs ~f:(fun reg ->
      sub_llvars :=
        StrMap.add
          (bb_phi_reg_name reg blk_tid)
          (Llvm.undef (var_lltype llvm_ctx reg))
          !sub_llvars)

let create_fun llvm_ctx llvm_module sub =
  let tid = Term.tid sub in
  let ret_typ = create_ret_type llvm_ctx in
  let args_typ = create_arg_types llvm_ctx tid in
  let fn_typ = Llvm.function_type ret_typ args_typ in
  let fn = Llvm.define_function (Sub.name sub) fn_typ llvm_module in
  set_arg_names fn tid;
  ll_funcs := StrMap.add (Sub.name sub) (fn, fn_typ) !ll_funcs

let set_sub llvm_ctx llvm_module sub =
  let free_vars = free_vars sub in
  let ret = Arg.create ~intent:Out !ret_reg (Var !ret_reg) in
  if Term.tid sub |> Tid.name = "@main" then
    let rdi = Var.create "RDI" (Imm 64) in
    let rsi = Var.create "RSI" (Imm 64) in
    subs :=
      StrMap.add
        (Term.tid sub |> Tid.name)
        ( [ ret ],
          [
            Arg.create ~intent:In rdi (Var rdi);
            Arg.create ~intent:In rsi (Var rsi);
          ] )
        !subs
  else
    subs :=
      StrMap.add
        (Term.tid sub |> Tid.name)
        ( [ ret ],
          Base.List.map
            ~f:(fun reg -> Arg.create ~intent:In reg (Var reg))
            free_vars )
        !subs;
  create_fun llvm_ctx llvm_module sub

module type Abi = sig
  val return : Decl_parser.functype -> var list

  val args :
    Decl_parser.functype list -> Decl_parser.functype -> (exp * intent) list
end

let arg_type (exp : exp) =
  match exp with
  | Int i -> Imm (Word.bitwidth i)
  | Var v -> Var.typ v
  | Load (_, _, _, size) -> Imm (Size.in_bits size)
  | _ -> failwith "pp exp type: non-imm var"

let set_libc llvm_ctx llvm_module target libc =
  let abi =
    if Theory.Target.matches target "x86_64-gnu-elf" then
      (module Gnu64_abi : Abi)
    else failwith "abi not supported"
  in
  let module Abi = (val abi : Abi) in
  StrMap.iter
    (fun name (data : Decl_parser.funcdef) ->
      let ret = Abi.return data.return in
      let args = Abi.args data.args data.return in
      let ret_typ = Decl_parser.functype_to_lltype llvm_ctx data.return in
      let args_typ =
        Base.List.map
          ~f:(fun typ -> Decl_parser.functype_to_lltype llvm_ctx typ)
          data.args
      in
      let fn_typ = Llvm.function_type ret_typ (Array.of_list args_typ) in
      let fn = Llvm.declare_function (sanitize_name name) fn_typ llvm_module in
      ll_funcs := StrMap.add name (fn, fn_typ) !ll_funcs;
      let func_decl =
        ( List.map (fun r -> Arg.create ~intent:Out r (Var r)) ret,
          List.mapi
            (fun i (a, intent) ->
              let arg_var =
                Var.create (name ^ sprintf "arg%d" i) (arg_type a)
              in
              Arg.create ~intent arg_var a)
            args )
      in
      subs := StrMap.add ("@" ^ name) func_decl !subs)
    libc

let stack_len = 0x2048
let stack_off = 0x5000

let correct_registers tid regs =
  object
    inherit Exp.mapper

    method! map_var var =
      if Var.same var !ret_reg then Var (create_ret var ~tid ~typ:(Var.typ var))
      else if Base.List.mem regs var ~equal:Var.same then
        Var (create_phi_reg var ~tid ~typ:(Var.typ var))
      else Var var
  end

let create_binop llvm_builder res_name (op, llvm_val1, llvm_val2) =
  match op with
  | PLUS -> Llvm.build_add llvm_val1 llvm_val2 res_name llvm_builder
  | MINUS -> Llvm.build_sub llvm_val1 llvm_val2 res_name llvm_builder
  | TIMES -> Llvm.build_mul llvm_val1 llvm_val2 res_name llvm_builder
  | DIVIDE -> Llvm.build_udiv llvm_val1 llvm_val2 res_name llvm_builder
  | SDIVIDE -> Llvm.build_sdiv llvm_val1 llvm_val2 res_name llvm_builder
  | MOD -> Llvm.build_urem llvm_val1 llvm_val2 res_name llvm_builder
  | SMOD -> Llvm.build_srem llvm_val1 llvm_val2 res_name llvm_builder
  | AND -> Llvm.build_and llvm_val1 llvm_val2 res_name llvm_builder
  | OR -> Llvm.build_or llvm_val1 llvm_val2 res_name llvm_builder
  | XOR -> Llvm.build_xor llvm_val1 llvm_val2 res_name llvm_builder
  | LSHIFT -> Llvm.build_lshr llvm_val1 llvm_val2 res_name llvm_builder
  | RSHIFT -> Llvm.build_shl llvm_val1 llvm_val2 res_name llvm_builder
  | ARSHIFT -> Llvm.build_ashr llvm_val1 llvm_val2 res_name llvm_builder
  | EQ -> Llvm.build_icmp Llvm.Icmp.Eq llvm_val1 llvm_val2 res_name llvm_builder
  | NEQ ->
      Llvm.build_icmp Llvm.Icmp.Ne llvm_val1 llvm_val2 res_name llvm_builder
  | LT ->
      Llvm.build_icmp Llvm.Icmp.Ult llvm_val1 llvm_val2 res_name llvm_builder
  | SLT ->
      Llvm.build_icmp Llvm.Icmp.Slt llvm_val1 llvm_val2 res_name llvm_builder
  | LE ->
      Llvm.build_icmp Llvm.Icmp.Ule llvm_val1 llvm_val2 res_name llvm_builder
  | SLE ->
      Llvm.build_icmp Llvm.Icmp.Sle llvm_val1 llvm_val2 res_name llvm_builder

let create_unop llvm_builder res_name (op, llvm_val) =
  match op with
  | NEG -> Llvm.build_neg llvm_val res_name llvm_builder
  | NOT -> Llvm.build_not llvm_val res_name llvm_builder

let create_concat llvm_builder (res_name, llvm_var1, llvm_var2) =
  let llvm_var1_size = Llvm.type_of llvm_var1 |> Llvm.size_of in
  let llvm_var2_size = Llvm.type_of llvm_var2 |> Llvm.size_of in
  let result_typ =
    Llvm.const_add llvm_var1_size llvm_var2_size |> Llvm.type_of
  in
  let zext_var1 = Llvm.build_zext llvm_var1 result_typ "" llvm_builder in
  let shl_var1 = Llvm.build_shl zext_var1 llvm_var2_size "" llvm_builder in
  let zext_var2 = Llvm.build_zext llvm_var2 result_typ "" llvm_builder in
  Llvm.build_or shl_var1 zext_var2 res_name llvm_builder

let create_extract llvm_ctx llvm_builder (res_name, hi, lo, llvm_var) =
  let temp_var =
    Llvm.build_lshr llvm_var
      (Llvm.const_int (Llvm.type_of llvm_var) lo)
      "" llvm_builder
  in
  let result_size = hi - lo + 1 in
  Llvm.build_trunc temp_var
    (Llvm.integer_type llvm_ctx result_size)
    res_name llvm_builder

let create_address_map_call llvm_ctx llvm_module llvm_builder llvm_var =
  let fn_typ =
    Llvm.function_type
      (Llvm.integer_type llvm_ctx !ptrsize)
      [| Llvm.integer_type llvm_ctx !ptrsize |]
  in
  let fn =
    Llvm.lookup_function "_address_map_" llvm_module
    |> Base.Option.value_exn ~message:"_address_map_ not found"
  in
  Llvm.build_call fn_typ fn [| llvm_var |] "" llvm_builder

let create_inttoptr llvm_ctx llvm_builder llvm_val =
  Llvm.build_inttoptr llvm_val (Llvm.pointer_type llvm_ctx) "" llvm_builder

let create_load llvm_ctx llvm_module llvm_builder (var_name, addr, size) =
  let addr =
    (* create_address_map_call llvm_ctx llvm_module llvm_builder addr *)
    create_inttoptr llvm_ctx llvm_builder addr
  in
  Llvm.build_load (Llvm.integer_type llvm_ctx size) addr var_name llvm_builder

let create_store llvm_ctx llvm_module llvm_builder (llvm_var, addr) =
  let addr =
    (* create_address_map_call llvm_ctx llvm_module llvm_builder addr *)
    create_inttoptr llvm_ctx llvm_builder addr
  in
  Llvm.build_store llvm_var addr llvm_builder

let create_cast llvm_ctx llvm_builder res_name (cast, i, llvm_val) =
  match cast with
  | UNSIGNED ->
      Llvm.build_zext llvm_val
        (Llvm.integer_type llvm_ctx i)
        res_name llvm_builder
  | SIGNED ->
      Llvm.build_sext llvm_val
        (Llvm.integer_type llvm_ctx i)
        res_name llvm_builder
  | HIGH ->
      (Llvm.build_lshr llvm_val
         (Llvm.const_int (Llvm.type_of llvm_val)
            (Llvm.integer_bitwidth (Llvm.type_of llvm_val) - i))
         "" llvm_builder
      |> Llvm.build_trunc)
        (Llvm.integer_type llvm_ctx i)
        res_name llvm_builder
  | LOW ->
      Llvm.build_trunc llvm_val
        (Llvm.integer_type llvm_ctx i)
        res_name llvm_builder

let rec create_exp ?res llvm_ctx llvm_module llvm_builder exp =
  let res_name = Base.Option.value res ~default:"" in
  match exp with
  | BinOp (op, e1, e2) ->
      let var1 = create_exp llvm_ctx llvm_module llvm_builder e1 in
      let var2 = create_exp llvm_ctx llvm_module llvm_builder e2 in
      create_binop llvm_builder res_name (op, var1, var2)
  | UnOp (op, e) ->
      let var = create_exp llvm_ctx llvm_module llvm_builder e in
      create_unop llvm_builder res_name (op, var)
  | Var v -> (
      let llvm_var =
        StrMap.find_opt (Var.name v) !sub_llvars
        |> Base.Option.value_exn
             ~message:("var " ^ Var.name v ^ " not found" ^ "\n")
      in
      match res with
      | Some res_name ->
          Llvm.build_add llvm_var
            (Llvm.const_int (Llvm.type_of llvm_var) 0)
            res_name llvm_builder
      | None -> llvm_var)
  | Int i ->
      Llvm.const_of_int64
        (Llvm.integer_type llvm_ctx (Word.bitwidth i))
        (Word.to_int64_exn i) true
  | Cast (cast, i, exp) ->
      let var = create_exp llvm_ctx llvm_module llvm_builder exp in
      create_cast llvm_ctx llvm_builder res_name (cast, i, var)
  | Concat (exp1, exp2) ->
      let llvm_var1 = create_exp llvm_ctx llvm_module llvm_builder exp1 in
      let llvm_var2 = create_exp llvm_ctx llvm_module llvm_builder exp2 in
      create_concat llvm_builder (res_name, llvm_var1, llvm_var2)
  | Extract (hi, lo, exp) ->
      let llvm_var = create_exp llvm_ctx llvm_module llvm_builder exp in
      create_extract llvm_ctx llvm_builder (res_name, hi, lo, llvm_var)
  | Store (_, addr, data, _, _) ->
      let addr = create_exp llvm_ctx llvm_module llvm_builder addr in
      let data = create_exp llvm_ctx llvm_module llvm_builder data in
      create_store llvm_ctx llvm_module llvm_builder (data, addr)
  | Load (_, addr, _, size) ->
      let addr = create_exp llvm_ctx llvm_module llvm_builder addr in
      create_load llvm_ctx llvm_module llvm_builder
        (res_name, addr, Size.in_bits size)
  | Let (var, exp, body) ->
      let unique_var =
        Var.create ~is_virtual:true ~fresh:true "" (Var.typ var)
      in
      let v =
        create_exp ~res:(Var.name unique_var) llvm_ctx llvm_module llvm_builder
          exp
      in
      sub_llvars := StrMap.add (Var.name unique_var) v !sub_llvars;
      let body = Exp.substitute (Var var) (Var unique_var) body in
      create_exp ~res:res_name llvm_ctx llvm_module llvm_builder body
  | Unknown (str, _) -> failwith @@ sprintf "Unknown: %s\n" str
  | _ -> failwith "pp_exp: Ite expressions"

let goto_label_exn jmp =
  match jmp with Goto l -> l | _ -> failwith "goto_label_exn: ret jmp"

let call_exn jmp =
  match Jmp.kind jmp with Call j -> j | _ -> failwith "call_exn:"

let label_tid label =
  match label with
  | Direct tid -> tid
  | Indirect _ -> failwith "label_tid: indirect label"

let llbb_from_tid fn tid =
  let bbs = Llvm.basic_blocks fn in
  Base.Array.find_exn bbs ~f:(fun bb ->
      Llvm.value_of_block bb |> Llvm.value_name = Tid.name tid)

let create_branches llvm_ctx llvm_module llvm_builder fn branches =
  if Seq.length branches = 1 then (* unconditional branch *)
    let br = Seq.hd_exn branches in
    let jmp__target = Jmp.kind br |> goto_label_exn |> label_tid in
    let bb = llbb_from_tid fn jmp__target in
    Llvm.build_br bb llvm_builder |> ignore
  else if Seq.length branches = 2 then
    (* conditional branch *)
    let br1 = Seq.hd_exn branches in
    let else_jmp = Seq.to_list branches |> Base.List.last_exn in
    let true_target = Jmp.kind br1 |> goto_label_exn |> label_tid in
    let false_target = Jmp.kind else_jmp |> goto_label_exn |> label_tid in
    let true_bb = llbb_from_tid fn true_target in
    let false_bb = llbb_from_tid fn false_target in
    let cond = Jmp.cond br1 in
    let cond_res = create_exp llvm_ctx llvm_module llvm_builder cond in
    Llvm.build_cond_br cond_res true_bb false_bb llvm_builder |> ignore
  else failwith "pp_branches: more than 2 branches"

let is_void tid = get_rets tid = []

type cf_type = Br | Ret | Call | Int | CallVoid | CallRet

let cf_type control_flow =
  let br = Seq.hd_exn control_flow in
  match Jmp.kind br with
  | Goto _ -> Br
  | Ret _ -> Ret
  | Call c -> (
      match Call.return c with
      | Some _ -> (
          match Call.target c with
          | Direct tid -> if is_void tid then CallVoid else Call
          | Indirect _ -> Call)
      | None -> CallRet)
  | Int _ -> Int

let create_def llvm_ctx llvm_module llvm_builder def =
  let var = Def.lhs def in
  let res =
    create_exp ~res:(Var.name var) llvm_ctx llvm_module llvm_builder
      (Def.rhs def)
  in
  sub_llvars := StrMap.add (Var.name var) res !sub_llvars

(* TODO *)
let create_call_args llvm_ctx llvm_module llvm_builder call_tid blk_tid =
  let args = get_args call_tid in
  Base.List.fold_right ~init:[] args ~f:(fun arg arg_list ->
      match Arg.intent arg with
      | Some i -> (
          match i with
          | Out -> arg_list
          | In | Both ->
              let var = Arg.lhs arg in
              let exp =
                Exp.map (correct_registers blk_tid !regs) (Arg.rhs arg)
              in
              let arg = create_exp llvm_ctx llvm_module llvm_builder exp in
              Llvm.set_value_name (bb_arg_name var blk_tid) arg;
              arg :: arg_list)
      | None -> arg_list)

let create_func_call llvm_ctx llvm_module llvm_builder current_fn blk_tid
    fallthrough target =
  let args =
    create_call_args llvm_ctx llvm_module llvm_builder target blk_tid
  in
  if is_void target then (
    let func_name = sanitize_name @@ Tid.name target in
    let fn, fn_typ = StrMap.find func_name !ll_funcs in
    Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder |> ignore;
    let bb = llbb_from_tid current_fn fallthrough in
    Llvm.build_br bb llvm_builder |> ignore)
  else
    let func_name = sanitize_name @@ Tid.name target in
    let fn, fn_typ = StrMap.find func_name !ll_funcs in
    let ret_var =
      Llvm.build_call fn_typ fn (Array.of_list args)
        (bb_phi_reg_name !ret_reg blk_tid)
        llvm_builder
    in
    Llvm.add_call_site_attr ret_var
      (Llvm.create_enum_attr llvm_ctx "zeroext" 0L)
      Llvm.AttrIndex.Return;
    sub_llvars :=
      StrMap.add (bb_phi_reg_name !ret_reg blk_tid) ret_var !sub_llvars;
    let bb = llbb_from_tid current_fn fallthrough in
    Llvm.build_br bb llvm_builder |> ignore

let create_call llvm_ctx llvm_module llvm_builder fn blk_tid call =
  match (Call.return call, Call.target call) with
  | None, _ ->
      let ret_var = llvar_from_name (bb_phi_reg_name !ret_reg blk_tid) in
      Llvm.build_ret ret_var llvm_builder |> ignore
  | Some (Direct ret_label), Direct target_label ->
      create_func_call llvm_ctx llvm_module llvm_builder fn blk_tid ret_label
        target_label
  | _, _ -> failwith "pp_call: non-trivial return type"

let create_phi llvm_ctx llvm_module llvm_builder fn phi =
  let var = Phi.lhs phi in
  if is_mem var || Base.List.mem !regs var ~equal:Var.same then ()
  else
    let vals = Phi.values phi in
    let values =
      Seq.fold vals ~init:[] ~f:(fun val_list (tid, exp) ->
          ( create_exp llvm_ctx llvm_module llvm_builder exp,
            llbb_from_tid fn tid )
          :: val_list)
    in
    let res =
      Llvm.build_phi values (sanitize_name @@ Var.name var) llvm_builder
    in
    sub_llvars := StrMap.add (sanitize_name @@ Var.name var) res !sub_llvars

let call_exn jmp =
  match Jmp.kind jmp with Call j -> j | _ -> failwith "call_exn:"

let base_exp_sub base_var sub =
  object
    inherit Exp.mapper
    method! map_var var = if Var.same var base_var then Var sub else Var var
  end

let update_args sub =
  let builder =
    Sub.Builder.create ~tid:(Term.tid sub) ~name:(Sub.name sub) ()
  in
  Seq.iter (Term.enum blk_t sub) ~f:(fun blk -> Sub.Builder.add_blk builder blk);
  Sub.Builder.result builder

let entry_blk_tid sub =
  let blks = Term.enum blk_t sub in
  Term.tid (Seq.hd_exn blks)

(* TODO *)
let update_rets sub =
  let sub_builder =
    Sub.Builder.create ~tid:(Term.tid sub) ~name:(Sub.name sub) ()
  in
  let new_blks = ref [] in
  let sub =
    Term.map blk_t sub ~f:(fun blk ->
        let builder = Blk.Builder.init ~copy_phis:true ~copy_defs:true blk in
        let control_flow = Term.enum jmp_t blk in
        (match cf_type control_flow with
        | CallRet -> (
            let jmp =
              Base.Option.value_exn ~message:"ret jmp not found"
                (Term.first jmp_t blk)
            in
            let call = jmp |> call_exn in
            match Call.target call with
            | Direct _ ->
                let temp_builder = Blk.Builder.create () in
                Blk.Builder.add_jmp temp_builder
                  (Jmp.create_ret
                     (Indirect (Var (Var.create "ret" (Var.typ !ret_reg)))));
                let new_blk = Blk.Builder.result temp_builder in
                new_blks := new_blk :: !new_blks;
                let call = Call.with_return call (Direct (Term.tid new_blk)) in
                Blk.Builder.add_jmp builder (Jmp.create_call call)
            | Indirect _ -> Blk.Builder.add_jmp builder jmp)
        | _ ->
            Seq.iter (Term.enum jmp_t blk) ~f:(fun jmp ->
                Blk.Builder.add_jmp builder jmp));
        Blk.Builder.result builder)
  in
  Seq.iter (Term.enum blk_t sub) ~f:(fun blk ->
      Sub.Builder.add_blk sub_builder blk);
  Base.List.iter !new_blks ~f:(fun blk -> Sub.Builder.add_blk sub_builder blk);
  Seq.iter (Term.enum arg_t sub) ~f:(fun arg ->
      Sub.Builder.add_arg sub_builder arg);
  Sub.Builder.result sub_builder

let update_main sub =
  if Sub.name sub = "main" then
    let entry_tid =
      Base.Option.value_exn ~message:"Main function has no blocks"
        (Sub.to_graph sub |> Graphs.Tid.Node.succs Graphs.Tid.start |> Seq.hd)
    in
    Term.map blk_t sub ~f:(fun blk ->
        if Term.tid blk = entry_tid then (
          let builder = Blk.Builder.init ~copy_phis:true ~copy_jmps:true blk in
          let arg_var_fp =
            create_arg !fp ~typ:(Var.typ !fp) ~tid:(Term.tid sub)
          in
          let arg_var_sp =
            create_arg !sp ~typ:(Var.typ !sp) ~tid:(Term.tid sub)
          in
          let stack_ptr = Var.create "stack_ptr" (Var.typ !sp) in
          let stack_exp =
            Bil.BinOp
              ( Bil.PLUS,
                Bil.Var stack_ptr,
                Bil.Int (Word.of_int ~width:(var_size !sp) (stack_len - 1)) )
          in
          let sp_def = Def.create arg_var_sp stack_exp in
          let fp_def =
            Def.create arg_var_fp
              (Bil.Int (Word.of_int ~width:(var_size !fp) 0))
          in
          Blk.Builder.add_def builder sp_def;
          Blk.Builder.add_def builder fp_def;
          Term.enum def_t blk
          |> Seq.iter ~f:(fun def -> Blk.Builder.add_def builder def);
          Blk.Builder.result builder)
        else blk)
  else sub

let transfer_regs sub =
  Term.map blk_t sub ~f:(fun blk ->
      let tid = Term.tid blk in
      let reg_map =
        ref
        @@ Base.List.fold !regs ~init:Var.Map.empty ~f:(fun map base ->
            let reg = create_reg base ~typ:(Var.typ base) ~tid in
            Var.Map.add_exn map ~key:base ~data:reg)
      in
      let blk =
        Base.List.fold ~init:blk !regs ~f:(fun blk base ->
            let ver = ref 0 in
            let reg = create_reg base ~typ:(Var.typ base) ~tid in
            Blk.map_elts blk ~def:(fun def ->
                let var = Def.lhs def in
                let exp = Def.rhs def in
                let def =
                  Def.with_rhs def
                    (Exp.map (base_exp_sub base (Var.with_index reg !ver)) exp)
                in
                let def =
                  if Var.same var base then (
                    let tmp =
                      Def.with_lhs def (Var.with_index reg (!ver + 1))
                    in
                    reg_map :=
                      Var.Map.change !reg_map (Var.base var) ~f:(fun _ ->
                          Some (Var.with_index reg (!ver + 1)));
                    ver := !ver + 1;
                    tmp)
                  else def
                in
                def))
      in
      let builder =
        Blk.Builder.init ~same_tid:true ~copy_phis:false ~copy_defs:false
          ~copy_jmps:true blk
      in
      let cfg = Sub.to_graph sub in
      let blk_incoming = Graphs.Tid.Node.preds (Term.tid blk) cfg in
      (if not (Seq.to_list blk_incoming = [ Graphs.Tid.start ]) then
         Base.List.iter !regs ~f:(fun base ->
             let var = create_reg base ~typ:(Var.typ base) ~tid in
             let phi_rhs =
               Seq.fold blk_incoming ~init:[] ~f:(fun prev tid ->
                   let reg_var = create_phi_reg base ~typ:(Var.typ base) ~tid in
                   (tid, Bil.Var reg_var) :: prev)
             in
             let phi = Phi.of_list var phi_rhs in
             Blk.Builder.add_phi builder phi)
       else
         let free_vars = free_vars sub in
         Base.List.iter !regs ~f:(fun base ->
             let reg = create_reg base ~typ:(Var.typ base) ~tid in
             let def =
               if not @@ Base.List.mem free_vars base ~equal:Var.same then
                 let data = Bil.Int (Word.of_int ~width:(var_size base) 0) in
                 Def.create reg data
               else
                 let arg =
                   create_arg base ~typ:(Var.typ base) ~tid:(Term.tid sub)
                 in
                 Def.create reg (Var arg)
             in
             Blk.Builder.add_def builder def));
      Blk.elts blk
      |> Seq.iter ~f:(fun elt ->
          match elt with `Def def -> Blk.Builder.add_def builder def | _ -> ());
      Var.Map.iteri !reg_map ~f:(fun ~key ~data ->
          match (cf_type (Term.enum jmp_t blk), Var.same key !ret_reg) with
          | Call, true ->
              let ret_var = create_ret key ~typ:(Var.typ key) ~tid in
              let def = Def.create ret_var (Var data) in
              Blk.Builder.add_def builder def
          | _, _ ->
              let reg_var = create_phi_reg key ~typ:(Var.typ key) ~tid in
              let def = Def.create reg_var (Var data) in
              Blk.Builder.add_def builder def);
      Blk.Builder.result builder)

let create_basicblocks llvm_ctx llvm_module llvm_builder blks fn =
  (* populate them with instructions *)
  Seq.iter blks ~f:(fun blk ->
      let bb = llbb_from_tid fn (Term.tid blk) in
      Llvm.position_at_end bb llvm_builder;
      Blk.elts blk
      |> Seq.iter ~f:(fun elt ->
          match elt with
          | `Def def -> create_def llvm_ctx llvm_module llvm_builder def
          | `Phi phi -> create_phi llvm_ctx llvm_module llvm_builder fn phi
          | `Jmp _ -> ());
      let control_flow = Term.enum jmp_t blk in
      match cf_type control_flow with
      | Br -> create_branches llvm_ctx llvm_module llvm_builder fn control_flow
      | Ret -> failwith "jmp: RET not implemented"
      | Int -> failwith "jmp: INT not implemented"
      | Call | CallVoid | CallRet ->
          let call = Seq.hd_exn control_flow |> call_exn in
          create_call llvm_ctx llvm_module llvm_builder fn (Term.tid blk) call)

let initialize_bbs llvm_ctx blks fn =
  (* create the basic blocks *)
  Seq.iter blks ~f:(fun blk ->
      Llvm.append_block llvm_ctx (Term.name blk) fn |> ignore)

let create_sub llvm_ctx llvm_module stack_ptr sub =
  let blks = Term.enum blk_t sub in
  let fn =
    Llvm.lookup_function (Sub.name sub) llvm_module
    |> Base.Option.value_exn ~message:"create sub : function not found"
  in
  let llvm_builder = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in
  (* reset sub_llvars *)
  sub_llvars := StrMap.empty;
  (* add stack_ptr to llvars *)
  sub_llvars :=
    StrMap.add "stack_ptr"
      (Llvm.build_ptrtoint stack_ptr (Llvm.i64_type llvm_ctx) "" llvm_builder)
      !sub_llvars;
  (* add args to llvars *)
  add_args_to_vars fn;
  initialize_bbs llvm_ctx blks fn;
  (* go from entry to first bb *)
  Llvm.build_br (llbb_from_tid fn (entry_blk_tid sub)) llvm_builder |> ignore;
  Seq.iter blks ~f:(fun blk -> add_regs_to_vars llvm_ctx (Term.tid blk));
  create_basicblocks llvm_ctx llvm_module llvm_builder blks fn

let is_libc libc sub =
  StrMap.mem (Sub.name sub) libc
  || Base.String.is_substring ~substring:":external" (Sub.name sub)

let create_llvm_i8array llvm_ctx arr =
  Base.Array.map arr ~f:(fun v -> Llvm.const_int (Llvm.i8_type llvm_ctx) v)
  |> Llvm.const_array (Llvm.i8_type llvm_ctx)

let create_global ~is_const llvm_ctx llvm_module mem name =
  let ret =
    Llvm.declare_global
      (Llvm.array_type (Llvm.i8_type llvm_ctx) (Array.length mem))
      name llvm_module
  in
  Llvm.set_initializer (create_llvm_i8array llvm_ctx mem) ret;
  Llvm.set_global_constant is_const ret;
  ret

let get_bil_pass name =
  Base.List.find_exn ~f:(fun pass -> Bil.Pass.name pass = name) (Bil.passes ())

let get_pass name =
  Project.find_pass name
  |> Base.Option.value_exn ~message:("pass " ^ name ^ " not found")

let run_pass proj name =
  let pass = get_pass name in
  Project.Pass.run_exn pass proj

let create_prog llvm_ctx llvm_module prog stack_ptr =
  Seq.iter ~f:(create_sub llvm_ctx llvm_module stack_ptr) (Term.enum sub_t prog)

let setup llvm_ctx llvm_module proj libc =
  let target = Project.target proj in
  set_ret_reg target;
  set_regs target;
  set_stack target;
  set_sp target;
  set_fp target;
  set_mem target;
  set_ptrsize target;
  set_libc llvm_ctx llvm_module target libc

let create_address_map llvm_ctx llvm_module target rodata_ptr data_ptr
    rodata_mem data_mem =
  let ptr_size = Theory.Target.bits target in
  let ptr_typ = Llvm.integer_type llvm_ctx ptr_size in
  let rodata_min_addr = Memory.min_addr rodata_mem |> Word.to_int64_exn in
  let rodata_max_addr = Memory.max_addr rodata_mem |> Word.to_int64_exn in
  let data_min_addr = Memory.min_addr data_mem |> Word.to_int64_exn in
  let data_max_addr = Memory.max_addr data_mem |> Word.to_int64_exn in
  let fn_typ = Llvm.function_type ptr_typ [| ptr_typ |] in
  let addr_map_fun = Llvm.define_function "_address_map_" fn_typ llvm_module in
  let entry_block = Llvm.entry_block addr_map_fun in
  let llvm_builder = Llvm.builder_at_end llvm_ctx entry_block in
  let ptr = Llvm.param addr_map_fun 0 in
  let is_rodata1 =
    Llvm.build_icmp Llvm.Icmp.Uge ptr
      (Llvm.const_of_int64 (Llvm.i64_type llvm_ctx) rodata_min_addr false)
      "" llvm_builder
  in
  let is_rodata2 =
    Llvm.build_icmp Llvm.Icmp.Ule ptr
      (Llvm.const_of_int64 ptr_typ rodata_max_addr false)
      "" llvm_builder
  in
  let is_rodata = Llvm.build_and is_rodata1 is_rodata2 "" llvm_builder in
  let is_data1 =
    Llvm.build_icmp Llvm.Icmp.Uge ptr
      (Llvm.const_of_int64 ptr_typ data_min_addr false)
      "" llvm_builder
  in
  let is_data2 =
    Llvm.build_icmp Llvm.Icmp.Ule ptr
      (Llvm.const_of_int64 ptr_typ data_max_addr false)
      "" llvm_builder
  in
  let is_data = Llvm.build_and is_data1 is_data2 "" llvm_builder in
  let fallthrough1 = Llvm.append_block llvm_ctx "fallthrough1" addr_map_fun in
  let isrodata = Llvm.append_block llvm_ctx "isrodata" addr_map_fun in
  let fallthrough2 = Llvm.append_block llvm_ctx "fallthrough2" addr_map_fun in
  let isdata = Llvm.append_block llvm_ctx "isdata" addr_map_fun in
  Llvm.build_cond_br is_rodata isrodata fallthrough1 llvm_builder |> ignore;
  let llvm_builder = Llvm.builder_at_end llvm_ctx fallthrough1 in
  Llvm.build_cond_br is_data isdata fallthrough2 llvm_builder |> ignore;
  let llvm_builder = Llvm.builder_at_end llvm_ctx fallthrough2 in
  Llvm.build_ret ptr llvm_builder |> ignore;
  let llvm_builder = Llvm.builder_at_end llvm_ctx isrodata in
  let rodata_ptr = Llvm.build_ptrtoint rodata_ptr ptr_typ "" llvm_builder in
  let rodata_offset =
    Llvm.build_sub ptr
      (Llvm.const_of_int64 ptr_typ rodata_min_addr false)
      "" llvm_builder
  in
  let rodata_addr = Llvm.build_add rodata_ptr rodata_offset "" llvm_builder in
  Llvm.build_ret rodata_addr llvm_builder |> ignore;
  let llvm_builder = Llvm.builder_at_end llvm_ctx isdata in
  let data_ptr = Llvm.build_ptrtoint data_ptr ptr_typ "" llvm_builder in
  let data_offset =
    Llvm.build_sub ptr
      (Llvm.const_of_int64 ptr_typ data_min_addr false)
      "" llvm_builder
  in
  let data_addr = Llvm.build_add data_ptr data_offset "" llvm_builder in
  Llvm.build_ret data_addr llvm_builder |> ignore

let pp proj output_program =
  let proj = run_pass proj "trivial-condition-form" in
  let proj = run_pass proj "optimization" in
  (* print_sections proj; *)
  Project.passes ()
  |> Base.List.iter ~f:(fun pass ->
      eprintf "Project pass :: %s \n" (Project.Pass.name pass));
  let rodata = get_section ".rodata" proj in
  let data = get_section ".data" proj in
  let stack = Base.Array.create ~len:stack_len 0 in
  let libc = Decl_parser.parse_header_file "stdio_headers.ll" in
  let llvm_ctx = Llvm.create_context () in
  let llvm_module = Llvm.create_module llvm_ctx "Convlir" in
  setup llvm_ctx llvm_module proj libc;
  let prog = Project.program proj in
  let main =
    Base.Option.value_exn ~message:"Main function not found"
      (Term.enum sub_t prog |> Seq.find ~f:(fun sub -> Sub.name sub = "main"))
  in
  let reachable_funcs = Reachable_funcs.reachable_funcs prog main in
  SubSet.iter
    (fun sub ->
      if is_libc libc sub || not (SubSet.mem sub reachable_funcs) then ()
      else (
        Sub.pp err_formatter sub;
        set_sub llvm_ctx llvm_module sub))
    reachable_funcs;
  let proj =
    Project.map_program proj ~f:(fun prog ->
        Term.filter_map sub_t prog ~f:(fun sub ->
            if is_libc libc sub || not (SubSet.mem sub reachable_funcs) then
              None
            else
              Some
                (sub |> update_args |> update_rets |> Sub.ssa |> transfer_regs
               |> update_main)))
  in
  let rodata_ptr =
    create_global ~is_const:true llvm_ctx llvm_module rodata "rodata"
  in
  let data_ptr =
    create_global ~is_const:false llvm_ctx llvm_module data "data"
  in
  let stack_ptr =
    create_global ~is_const:false llvm_ctx llvm_module stack "stack"
  in
  eprintf "llvm module created\n";
  (* create_address_map llvm_ctx llvm_module (Project.target proj) rodata_ptr *)
  (*   data_ptr *)
  (*   (get_section_mem ".rodata" proj) *)
  (*   (get_section_mem ".data" proj); *)
  create_prog llvm_ctx llvm_module (Project.program proj) stack_ptr;
  Llvm.print_module output_program llvm_module;
  Llvm.dispose_module llvm_module;
  Llvm.dispose_context llvm_ctx

let main input_program output_program _ =
  Bil.passes ()
  |> Base.List.iter ~f:(fun pass ->
      eprintf "Bil pass :: %s \n" (Bil.Pass.name pass));
  let passes =
    Base.List.map ~f:get_bil_pass
      [
        "bnf1";
        "constant-folding";
        "constant-propagation";
        "prune-dead-virtuals";
      ]
  in
  Bil.select_passes passes;
  let loader = "llvm" in
  let proj =
    Project.create @@ Project.Input.load input_program ~loader
    |> Core.Or_error.ok_exn
  in
  pp proj output_program;
  Ok ()

let features_used =
  [
    "semantics";
    "function-starts";
    "disassembler";
    "lifter";
    "symbolizer";
    "rooter";
    "reconstructor";
    "brancher";
    "loader";
    "abi";
  ]

let input =
  Extension.Command.argument
    Extension.Type.("input file" %: string)
    ~doc:"Executable to convert to LLVM IR"

let output =
  Extension.Command.argument
    Extension.Type.("output file" %: string)
    ~doc:"File to output LLVM IR"

let () =
  Extension.Command.declare "convlir"
    (args $ input $ output)
    main ~doc:"Convert a binary to LLVM IR" ~requires:features_used

let () = Extension.declare ~provides:[ "command" ] (fun _ -> Ok ())
