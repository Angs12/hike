open Bap.Std.Bil.Types
open Bap.Std
open X86Regs
open Convutils
module StrMap = Map.Make (String)

let sub_llvars = ref @@ StrMap.empty
let ll_funcs = ref @@ StrMap.empty
let llvar_from_name name = StrMap.find name !sub_llvars

let typ_lltype llvm_ctx typ =
  match typ with
  | Imm n -> Llvm.integer_type llvm_ctx n
  | _ -> failwith "typ_lltype : non-imm typ"

let var_lltype llvm_ctx var = typ_lltype llvm_ctx (Var.typ var)

let llbb_from_tid fn tid =
  let bbs = Llvm.basic_blocks fn in
  Base.Array.find_exn bbs ~f:(fun bb ->
      Llvm.value_of_block bb |> Llvm.value_name = Tid.name tid)

let create_ret_type llvm_ctx = var_lltype llvm_ctx !ret_reg

let create_arg_types llvm_ctx sub_tid =
  let args = get_args sub_tid in
  Base.List.to_array args
  |> Base.Array.map ~f:(fun arg ->
      let var = Arg.lhs arg in
      if Arg.intent arg = Some Both then Llvm.pointer_type llvm_ctx
      else var_lltype llvm_ctx var)

let set_arg_names fn sub_tid =
  let args = get_args sub_tid in
  Base.List.iteri args ~f:(fun i arg ->
      let param = Llvm.param fn i in
      Llvm.set_value_name (bb_arg_name (Arg.lhs arg) sub_tid) param)

let set_arg_attrs llvm_ctx fn sub_tid =
  let args = get_args sub_tid in
  Base.List.iteri args ~f:(fun i arg ->
      if Arg.intent arg = Some Both then
        let attr = Llvm.create_enum_attr llvm_ctx "noalias" 0L in
        Llvm.add_function_attr fn attr (Llvm.AttrIndex.Param i))

let add_args_to_vars llvm_ctx llvm_builder fn =
  Llvm.iter_params
    (fun param ->
      let name = Llvm.value_name param in
      match Llvm.classify_type (Llvm.type_of param) with
      | Llvm.TypeKind.Pointer ->
          sub_llvars :=
            StrMap.add name
              (Llvm.build_ptrtoint param
                 (Llvm.integer_type llvm_ctx !ptrsize)
                 "" llvm_builder)
              !sub_llvars
      | _ -> sub_llvars := StrMap.add name param !sub_llvars)
    fn

let add_regs_to_vars llvm_ctx blk_tid =
  Base.List.iter !base_regs ~f:(fun reg ->
      let undef = Llvm.undef (var_lltype llvm_ctx reg) in
      sub_llvars := StrMap.add (bb_reg_name reg blk_tid) undef !sub_llvars)

let create_fun llvm_ctx llvm_module sub =
  let tid = Term.tid sub in
  let ret_typ = create_ret_type llvm_ctx in
  let args_typ = create_arg_types llvm_ctx tid in
  let fn_typ = Llvm.function_type ret_typ args_typ in
  let fn = Llvm.define_function (Sub.name sub) fn_typ llvm_module in
  set_arg_names fn tid;
  set_arg_attrs llvm_ctx fn tid;
  ll_funcs := StrMap.add (Sub.name sub) (fn, fn_typ) !ll_funcs

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
  | LSHIFT -> Llvm.build_shl llvm_val1 llvm_val2 res_name llvm_builder
  | RSHIFT -> Llvm.build_lshr llvm_val1 llvm_val2 res_name llvm_builder
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

let create_inttoptr llvm_ctx llvm_builder llvm_val =
  Llvm.build_inttoptr llvm_val (Llvm.pointer_type llvm_ctx) "" llvm_builder

let create_load llvm_ctx llvm_builder (var_name, addr, size) =
  let addr = create_inttoptr llvm_ctx llvm_builder addr in
  Llvm.build_load (Llvm.integer_type llvm_ctx size) addr var_name llvm_builder

let create_store llvm_ctx llvm_builder (llvm_var, addr) =
  let addr = create_inttoptr llvm_ctx llvm_builder addr in
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
  | Var v ->
      StrMap.find_opt (Var.name v) !sub_llvars
      |> Base.Option.value_exn ~message:("var " ^ Var.name v ^ " not found")
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
      create_store llvm_ctx llvm_builder (data, addr)
  | Load (_, addr, _, size) ->
      let addr = create_exp llvm_ctx llvm_module llvm_builder addr in
      create_load llvm_ctx llvm_builder (res_name, addr, Size.in_bits size)
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
  | Unknown (_, typ) -> Llvm.undef (typ_lltype llvm_ctx typ)
  | _ -> failwith "pp_exp: Ite expressions"

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

let create_def llvm_ctx llvm_module llvm_builder def =
  let var = Def.lhs def in
  let res =
    create_exp ~res:(Var.name var) llvm_ctx llvm_module llvm_builder
      (Def.rhs def)
  in
  sub_llvars := StrMap.add (Var.name var) res !sub_llvars

let create_call_args llvm_ctx llvm_module llvm_builder call_tid blk_tid =
  let args = get_args call_tid in
  Base.List.fold_right ~init:[] args ~f:(fun arg arg_list ->
      match Arg.intent arg with
      | Some i -> (
          match i with
          | Out -> arg_list
          | In | Both ->
              let var = Arg.lhs arg in
              let exp = Exp.map (correct_registers blk_tid) (Arg.rhs arg) in
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

let update_phis llvm_ctx llvm_module llvm_builder fn phi =
  let var = Phi.lhs phi in
  let vals = Phi.values phi in
  let phi_llvar = llvar_from_name (sanitize_name @@ Var.name var) in
  Seq.iter vals ~f:(fun (tid, exp) ->
      Llvm.add_incoming
        (create_exp llvm_ctx llvm_module llvm_builder exp, llbb_from_tid fn tid)
        phi_llvar)

let create_empty_phi llvm_ctx llvm_builder phi =
  let var = Phi.lhs phi in
  let res =
    Llvm.build_empty_phi (var_lltype llvm_ctx var)
      (sanitize_name @@ Var.name var)
      llvm_builder
  in
  sub_llvars := StrMap.add (sanitize_name @@ Var.name var) res !sub_llvars

let create_basicblocks llvm_ctx llvm_module llvm_builder blks fn =
  (* populate them with instructions *)
  Seq.iter blks ~f:(fun blk ->
      let bb = llbb_from_tid fn (Term.tid blk) in
      Llvm.position_at_end bb llvm_builder;
      Blk.elts blk
      |> Seq.iter ~f:(fun elt ->
          match elt with
          | `Def def -> create_def llvm_ctx llvm_module llvm_builder def
          | `Phi phi -> create_empty_phi llvm_ctx llvm_builder phi
          | `Jmp _ -> ());
      let control_flow = Term.enum jmp_t blk in
      match cf_type control_flow with
      | Br -> create_branches llvm_ctx llvm_module llvm_builder fn control_flow
      | Ret -> failwith "jmp: RET not implemented"
      | Int -> failwith "jmp: INT not implemented"
      | Call | CallVoid | CallRet ->
          let call = Seq.hd_exn control_flow |> call_exn in
          create_call llvm_ctx llvm_module llvm_builder fn (Term.tid blk) call);
  Seq.iter blks ~f:(fun blk ->
      let bb = llbb_from_tid fn (Term.tid blk) in
      Llvm.position_at_end bb llvm_builder;
      Blk.elts blk
      |> Seq.iter ~f:(fun elt ->
          match elt with
          | `Phi phi -> update_phis llvm_ctx llvm_module llvm_builder fn phi
          | _ -> ()))

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
  add_args_to_vars llvm_ctx llvm_builder fn;
  (* add regs to llvars *)
  Seq.iter blks ~f:(fun blk -> add_regs_to_vars llvm_ctx (Term.tid blk));
  initialize_bbs llvm_ctx blks fn;
  (* go from entry to first bb *)
  Llvm.build_br (llbb_from_tid fn (entry_blk_tid sub)) llvm_builder |> ignore;
  create_basicblocks llvm_ctx llvm_module llvm_builder blks fn

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

let create_prog llvm_ctx llvm_module prog stack_ptr =
  Seq.iter ~f:(create_sub llvm_ctx llvm_module stack_ptr) (Term.enum sub_t prog)
