open Bap.Std.Bil.Types
open Bap.Std
open Targetutils
open Convutils
module Reader = Monads.Std.Monad.Reader
module StrMap = Map.Make (String)

let ll_funcs = ref @@ StrMap.empty

let typ_lltype_m typ =
  let open Reader in
  let* llvm_ctx, _ = read () in
  match typ with
  | Imm n -> return @@ Llvm.integer_type llvm_ctx n
  | _ -> return @@ Llvm.pointer_type llvm_ctx

let var_lltype var = typ_lltype_m (Var.typ var)

let create_ret_type sub_tid =
  let open Reader in
  let* llvm_ctx, _ = read () in
  let rets = get_rets sub_tid in
  match rets with
  | [] -> return @@ Llvm.void_type llvm_ctx
  | [ ret ] -> var_lltype (Arg.lhs ret)
  | rets ->
      let* rets_typs =
        Reader.List.map rets ~f:(fun ret -> var_lltype (Arg.lhs ret))
      in
      return @@ Llvm.struct_type llvm_ctx (Array.of_list rets_typs)

let create_arg_types sub_tid =
  let open Reader in
  let* llvm_ctx, _ = read () in
  let args = get_args sub_tid in
  Reader.List.map args ~f:(fun arg ->
      let var = Arg.lhs arg in
      if Arg.intent arg = Some Both then return @@ Llvm.pointer_type llvm_ctx
      else var_lltype var)

let set_arg_names fn sub_tid =
  let args = get_args sub_tid in
  Base.List.iteri args ~f:(fun i arg ->
      let param = Llvm.param fn i in
      Llvm.set_value_name (Var.name (Arg.lhs arg)) param)

let set_arg_attrs fn sub_tid =
  let args = get_args sub_tid in
  let open Reader in
  let* llvm_ctx, _ = read () in
  Base.List.iteri args ~f:(fun i arg ->
      if Arg.intent arg = Some Both then
        let attr = Llvm.create_enum_attr llvm_ctx "noalias" 0L in
        Llvm.add_function_attr fn attr (Llvm.AttrIndex.Param i));
  return ()

let add_args_to_vars llvm_builder fn () =
  let open Reader in
  let* llvm_ctx, _ = read () in
  return
  @@ Llvm.iter_params
       (fun param ->
         let name = Llvm.value_name param in
         match Llvm.classify_type (Llvm.type_of param) with
         | Llvm.TypeKind.Pointer ->
             insert_llval_name name
               (Llvm.build_ptrtoint param
                  (Llvm.integer_type llvm_ctx !ptrsize)
                  "" llvm_builder)
         | _ -> insert_llval_name name param)
       fn

let create_fun_declaration sub_tid =
  let open Reader in
  let* _, llvm_module = read () in
  let* ret_typ = create_ret_type sub_tid in
  let* args_typ = create_arg_types sub_tid in
  let fn_typ = Llvm.function_type ret_typ (Array.of_list args_typ) in
  let fn =
    Llvm.declare_function (sanitize_name @@ Tid.name sub_tid) fn_typ llvm_module
  in
  ll_funcs :=
    StrMap.add (sanitize_name @@ Tid.name sub_tid) (fn, fn_typ) !ll_funcs;
  return ()

let create_fun sub_tid =
  let open Reader in
  let* llvm_ctx, llvm_module = read () in
  let* ret_typ = create_ret_type sub_tid in
  let* args_typ = create_arg_types sub_tid in
  let fn_typ = Llvm.function_type ret_typ (Array.of_list args_typ) in
  let fn =
    Llvm.define_function (sanitize_name @@ Tid.name sub_tid) fn_typ llvm_module
  in
  set_arg_names fn sub_tid;
  let attr = Llvm.create_enum_attr llvm_ctx "alwaysinline" 0L in
  Llvm.add_function_attr fn attr Llvm.AttrIndex.Function;
  ll_funcs :=
    StrMap.add (sanitize_name @@ Tid.name sub_tid) (fn, fn_typ) !ll_funcs;
  set_arg_attrs fn sub_tid >>= return

let create_binop llvm_builder (op, llvm_val1, llvm_val2) =
  Reader.return
  @@
  match op with
  | PLUS -> Llvm.build_add llvm_val1 llvm_val2 "" llvm_builder
  | MINUS -> Llvm.build_sub llvm_val1 llvm_val2 "" llvm_builder
  | TIMES -> Llvm.build_mul llvm_val1 llvm_val2 "" llvm_builder
  | DIVIDE -> Llvm.build_udiv llvm_val1 llvm_val2 "" llvm_builder
  | SDIVIDE -> Llvm.build_sdiv llvm_val1 llvm_val2 "" llvm_builder
  | MOD -> Llvm.build_urem llvm_val1 llvm_val2 "" llvm_builder
  | SMOD -> Llvm.build_srem llvm_val1 llvm_val2 "" llvm_builder
  | AND -> Llvm.build_and llvm_val1 llvm_val2 "" llvm_builder
  | OR -> Llvm.build_or llvm_val1 llvm_val2 "" llvm_builder
  | XOR -> Llvm.build_xor llvm_val1 llvm_val2 "" llvm_builder
  | LSHIFT ->
      let v2 =
        Llvm.build_sext llvm_val2 (Llvm.type_of llvm_val1) "" llvm_builder
      in
      Llvm.build_shl llvm_val1 v2 "" llvm_builder
  | RSHIFT ->
      let v2 =
        Llvm.build_sext llvm_val2 (Llvm.type_of llvm_val1) "" llvm_builder
      in
      Llvm.build_lshr llvm_val1 v2 "" llvm_builder
  | ARSHIFT ->
      let v2 =
        Llvm.build_sext llvm_val2 (Llvm.type_of llvm_val1) "" llvm_builder
      in
      Llvm.build_ashr llvm_val1 v2 "" llvm_builder
  | EQ -> Llvm.build_icmp Llvm.Icmp.Eq llvm_val1 llvm_val2 "" llvm_builder
  | NEQ -> Llvm.build_icmp Llvm.Icmp.Ne llvm_val1 llvm_val2 "" llvm_builder
  | LT -> Llvm.build_icmp Llvm.Icmp.Ult llvm_val1 llvm_val2 "" llvm_builder
  | SLT -> Llvm.build_icmp Llvm.Icmp.Slt llvm_val1 llvm_val2 "" llvm_builder
  | LE -> Llvm.build_icmp Llvm.Icmp.Ule llvm_val1 llvm_val2 "" llvm_builder
  | SLE -> Llvm.build_icmp Llvm.Icmp.Sle llvm_val1 llvm_val2 "" llvm_builder

let create_unop llvm_builder (op, llvm_val) =
  Reader.return
  @@
  match op with
  | NEG -> Llvm.build_neg llvm_val "" llvm_builder
  | NOT -> Llvm.build_not llvm_val "" llvm_builder

let create_concat llvm_builder (llvm_var1, llvm_var2) =
  let open Reader in
  let* llvm_ctx, _ = read () in
  let llvm_var1_size = Llvm.type_of llvm_var1 |> Llvm.integer_bitwidth in
  let llvm_var2_size = Llvm.type_of llvm_var2 |> Llvm.integer_bitwidth in
  let result_typ =
    Llvm.integer_type llvm_ctx (llvm_var1_size + llvm_var2_size)
  in
  let llvm_var2_sizeof = Llvm.const_int result_typ llvm_var2_size in
  let zext_var1 = Llvm.build_zext llvm_var1 result_typ "" llvm_builder in
  let shl_var1 = Llvm.build_shl zext_var1 llvm_var2_sizeof "" llvm_builder in
  let zext_var2 = Llvm.build_zext llvm_var2 result_typ "" llvm_builder in
  return @@ Llvm.build_or shl_var1 zext_var2 "" llvm_builder

let create_extract llvm_builder (hi, lo, llvm_var) =
  let open Reader in
  let* llvm_ctx, _ = read () in
  let temp_var =
    Llvm.build_lshr llvm_var
      (Llvm.const_int (Llvm.type_of llvm_var) lo)
      "" llvm_builder
  in
  let result_size = hi - lo + 1 in
  return
  @@ Llvm.build_trunc temp_var
       (Llvm.integer_type llvm_ctx result_size)
       "" llvm_builder

let create_inttoptr llvm_builder llvm_val =
  let open Reader in
  let* llvm_ctx, _ = read () in
  return
  @@ Llvm.build_inttoptr llvm_val (Llvm.pointer_type llvm_ctx) "" llvm_builder

let create_load llvm_builder (addr, size) =
  let open Reader in
  let* llvm_ctx, _ = read () in
  let* addr = create_inttoptr llvm_builder addr in
  return
  @@ Llvm.build_load (Llvm.integer_type llvm_ctx size) addr "" llvm_builder

let create_store llvm_builder (llvm_var, addr) =
  let open Reader in
  let* addr = create_inttoptr llvm_builder addr in
  return @@ Llvm.build_store llvm_var addr llvm_builder

let create_cast llvm_builder (cast, i, llvm_val) =
  let open Reader in
  let* llvm_ctx, _ = read () in
  match cast with
  | UNSIGNED ->
      return
      @@ Llvm.build_zext llvm_val (Llvm.integer_type llvm_ctx i) "" llvm_builder
  | SIGNED ->
      return
      @@ Llvm.build_sext llvm_val (Llvm.integer_type llvm_ctx i) "" llvm_builder
  | HIGH ->
      let lshr =
        Llvm.build_lshr llvm_val
          (Llvm.const_int (Llvm.type_of llvm_val)
             (Llvm.integer_bitwidth (Llvm.type_of llvm_val) - i))
          "" llvm_builder
      in
      return
      @@ Llvm.build_trunc lshr (Llvm.integer_type llvm_ctx i) "" llvm_builder
  | LOW ->
      return
      @@ Llvm.build_trunc llvm_val
           (Llvm.integer_type llvm_ctx i)
           "" llvm_builder

let create_immidiate word =
  let open Reader in
  let* llvm_ctx, _ = read () in
  return
  @@ Llvm.const_int_of_string
       (Llvm.integer_type llvm_ctx (Word.bitwidth word))
       (Word.string_of_value word)
       16

let rec create_exp llvm_builder exp =
  let open Reader in
  match exp with
  | BinOp (op, e1, e2) ->
      let* var1 = create_exp llvm_builder e1 in
      let* var2 = create_exp llvm_builder e2 in
      create_binop llvm_builder (op, var1, var2)
  | UnOp (op, e) ->
      let* var = create_exp llvm_builder e in
      create_unop llvm_builder (op, var)
  | Var v -> return @@ get_llval v
  | Int i -> create_immidiate i
  | Cast (cast, i, exp) ->
      let* var = create_exp llvm_builder exp in
      create_cast llvm_builder (cast, i, var)
  | Concat (exp1, exp2) ->
      let* llvm_var1 = create_exp llvm_builder exp1 in
      let* llvm_var2 = create_exp llvm_builder exp2 in
      create_concat llvm_builder (llvm_var1, llvm_var2)
  | Extract (hi, lo, exp) ->
      let* llvm_var = create_exp llvm_builder exp in
      create_extract llvm_builder (hi, lo, llvm_var)
  | Store (_, addr, data, _, _) ->
      let* addr = create_exp llvm_builder addr in
      let* data = create_exp llvm_builder data in
      create_store llvm_builder (data, addr)
  | Load (_, addr, _, size) ->
      let* addr = create_exp llvm_builder addr in
      create_load llvm_builder (addr, Size.in_bits size)
  | Let (var, exp, body) ->
      let unique_var =
        Var.create ~is_virtual:true ~fresh:true "" (Var.typ var)
      in
      let* v = create_exp llvm_builder exp in
      insert_var unique_var v;
      let body = Exp.substitute (Var var) (Var unique_var) body in
      create_exp llvm_builder body
  | Ite (cond, true_exp, false_exp) ->
      let* cond = create_exp llvm_builder cond in
      let* true_exp = create_exp llvm_builder true_exp in
      let* false_exp = create_exp llvm_builder false_exp in
      return @@ Llvm.build_select cond true_exp false_exp "" llvm_builder
  | Unknown (_, typ) ->
      let* typ = typ_lltype_m typ in
      return @@ Llvm.undef typ

let create_branches llvm_builder branches =
  let open Reader in
  let open Bap.Std in
  if Seq.length branches = 1 then (* unconditional branch *)
    (
    let br = Seq.hd_exn branches in
    let jmp_target = Jmp.kind br |> goto_label_exn in
    match jmp_target with
    | Direct tid ->
        let bb = get_bb tid in
        Llvm.build_br bb llvm_builder |> ignore;
        Reader.return ()
    | Indirect exp ->
        let* target_val = create_exp llvm_builder exp in
        Llvm.build_indirect_br target_val 1 llvm_builder |> ignore;
        Reader.return ())
  else if Seq.length branches = 2 then (
    (* conditional branch *)
    let br1 = Seq.hd_exn branches in
    let else_jmp = Seq.to_list branches |> Base.List.last_exn in
    let true_target = Jmp.kind br1 |> goto_label_exn |> label_tid in
    let false_target = Jmp.kind else_jmp |> goto_label_exn |> label_tid in
    let true_bb = get_bb true_target in
    let false_bb = get_bb false_target in
    let cond = Jmp.cond br1 in
    let* cond_res = create_exp llvm_builder cond in
    Llvm.build_cond_br cond_res true_bb false_bb llvm_builder |> ignore;
    Reader.return ())
  else failwith "pp_branches: more than 2 branches"

let create_def llvm_builder def =
  let open Reader in
  let var = Def.lhs def in
  let* res = create_exp llvm_builder (Def.rhs def) in
  insert_var var res;
  return ()

let create_call_args llvm_builder call_tid _ =
  let open Reader in
  let args = get_args call_tid in
  Reader.List.map args ~f:(fun arg ->
      let exp = Arg.rhs arg in
      let* arg = create_exp llvm_builder exp in
      return arg)

let get_func tid =
  let open Reader in
  let name = sanitize_name @@ Tid.name tid in
  if StrMap.mem name !ll_funcs then return @@ StrMap.find name !ll_funcs
  else
    let* _ = create_fun_declaration tid in
    return @@ StrMap.find name !ll_funcs

let create_indirect_call llvm_builder blk_tid call =
  let open Reader in
  let target = Call.target call |> label_exp in
  let fallthrough =
    Call.return call
    |> Base.Option.value_exn ~message:"Create call: expected call got return"
    |> label_tid
  in
  let* target_exp = create_exp llvm_builder target in
  let* func_ptr = create_inttoptr llvm_builder target_exp in
  let* _, fn_typ = get_func (Tid.for_name "indirect_call") in
  let bb = get_bb fallthrough in
  let rets = get_rets (Tid.for_name "indirect_call") in
  let* args =
    create_call_args llvm_builder (Tid.for_name "indirect_call") blk_tid
  in
  let ret_struct =
    Llvm.build_call fn_typ func_ptr (Array.of_list args) "" llvm_builder
  in
  Base.List.iteri rets ~f:(fun i ret ->
      let ret_val = Llvm.build_extractvalue ret_struct i "" llvm_builder in
      insert_var (Arg.lhs ret) ret_val);
  Llvm.build_br bb llvm_builder |> ignore;
  return ()

let create_func_call llvm_builder blk_tid fallthrough target =
  let open Reader in
  let* llvm_ctx, _ = read () in
  let* args = create_call_args llvm_builder target blk_tid in
  let rets = get_rets target in
  let* fn, fn_typ = get_func target in
  (match rets with
  | [] ->
      Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder |> ignore
  | [ ret ] ->
      let ret_var =
        Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
      in
      Llvm.add_call_site_attr ret_var
        (Llvm.create_enum_attr llvm_ctx "zeroext" 0L)
        Llvm.AttrIndex.Return;
      insert_var (Arg.lhs ret) ret_var
  | rets ->
      let ret_struct =
        Llvm.build_call fn_typ fn (Array.of_list args) "" llvm_builder
      in
      Base.List.iteri rets ~f:(fun i ret ->
          let ret_val = Llvm.build_extractvalue ret_struct i "" llvm_builder in
          insert_var (Arg.lhs ret) ret_val));
  (match fallthrough with
  | Some fallthrough ->
      let bb = get_bb fallthrough in
      Llvm.build_br bb llvm_builder |> ignore
  | None -> Llvm.build_unreachable llvm_builder |> ignore);
  return ()

let create_return llvm_builder cur_sub _ =
  let rets =
    get_rets (Term.tid cur_sub)
    |> Base.List.map ~f:(fun ret -> get_llval (Arg.lhs ret))
  in
  (match rets with
  | [] -> Llvm.build_ret_void llvm_builder |> ignore
  | [ ret ] -> Llvm.build_ret ret llvm_builder |> ignore
  | rets -> Llvm.build_aggregate_ret (Array.of_list rets) llvm_builder |> ignore);
  Reader.return ()

let create_call llvm_builder blk_tid call =
  let target = Call.target call |> label_tid in
  let fallthrough = Option.map label_tid (Call.return call) in
  create_func_call llvm_builder blk_tid fallthrough target

let update_phi blk_incoming blk_tid =
  let open Reader in
  List.iter !base_regs ~f:(fun base ->
      let phi_llvar = get_phi blk_tid base in
      Seq.iter blk_incoming ~f:(fun tid ->
          let phi_reg = get_phi_reg tid base in
          Llvm.add_incoming (phi_reg, get_bb tid) phi_llvar;
          return ()))

let setup_llvars llvm_builder stack_ptr fn () =
  (* reset sub_llvars *)
  clear_blk_llvars ();
  clear_sub_llvars ();
  (* add stack_ptr to llvars *)
  insert_llval_name "stack_ptr" stack_ptr;
  add_args_to_vars llvm_builder fn ()

let update_phis blks sub () =
  let open Reader in
  let cfg = Sub.to_graph sub in
  Seq.iter blks ~f:(fun blk ->
      let blk_tid = Term.tid blk in
      let blk_incoming = Graphs.Tid.Node.preds (Term.tid blk) cfg in
      update_phi blk_incoming blk_tid)

let save_regs blk_tid () =
  let open Reader in
  Base.List.iter !base_regs ~f:(fun base ->
      insert_phi_reg blk_tid base (get_llval base));
  return ()

let create_control_flow llvm_builder blk sub () =
  let control_flow = Term.enum jmp_t blk in
  match cf_type control_flow with
  | Br -> create_branches llvm_builder control_flow
  | Int -> failwith "jmp: INT not implemented"
  | Ret -> create_return llvm_builder sub (Term.tid blk)
  | CallIndirect ->
      let call = Bap.Std.Seq.hd_exn control_flow |> call_exn in
      create_indirect_call llvm_builder (Term.tid blk) call
  | CallFun | CallFunVoid ->
      let call = Bap.Std.Seq.hd_exn control_flow |> call_exn in
      create_call llvm_builder (Term.tid blk) call

let transfer_regs llvm_builder blk_tid () =
  let open Reader in
  List.iter !base_regs ~f:(fun base ->
      let* typ = var_lltype base in
      let res = Llvm.build_empty_phi typ "" llvm_builder in
      insert_phi blk_tid base res;
      insert_var base res;
      return ())

let create_elts llvm_builder blk () =
  let open Reader in
  Blk.elts blk
  |> Seq.iter ~f:(fun elt ->
      match elt with
      | `Def def -> create_def llvm_builder def
      | `Phi _ -> return ()
      | `Jmp _ -> return ())

let populate_blks blks sub () =
  let open Reader in
  let* llvm_ctx, _ = read () in
  Seq.iter blks ~f:(fun blk ->
      let llvm_builder = Llvm.builder_at_end llvm_ctx (get_bb (Term.tid blk)) in
      transfer_regs llvm_builder (Term.tid blk) ()
      >>= create_elts llvm_builder blk
      >>= create_control_flow llvm_builder blk sub
      >>= save_regs (Term.tid blk))

(* go from entry to first bb *)
let exit_entry llvm_builder sub () =
  Reader.return @@ Llvm.build_br (get_bb (entry_blk_tid sub)) llvm_builder

let build_entry_block llvm_builder sub () =
  let open Reader in
  (* Can remove in the future *)
  let args =
    get_args (Term.tid sub)
    @
    if Term.name sub = "@main" then
      let stack_ptr = Var.create "stack_ptr" (Var.typ !sp) in
      [ Arg.create !sp (Var stack_ptr) ]
    else []
  in
  let tid = Graphs.Tid.start in
  init_blk_llvals tid;
  Reader.List.iter !base_regs ~f:(fun base ->
      let arg =
        Base.List.find args ~f:(fun arg -> Var.same (Arg.lhs arg) base)
      in
      let llval =
        match arg with
        | Some arg -> create_exp llvm_builder (Arg.rhs arg)
        | None -> !$Llvm.undef (var_lltype base)
      in
      !$(insert_phi_reg tid base) llval)
  >>= exit_entry llvm_builder sub
  |> void

let initialize_bbs blks fn () =
  let open Reader in
  let* llvm_ctx, _ = read () in
  (* create the basic blocks *)
  clear_bbs ();
  Bap.Std.Seq.iter blks ~f:(fun blk ->
      let tid = Term.tid blk in
      init_blk_llvals tid;
      insert_bb tid
        (Llvm.append_block llvm_ctx (sanitize_name @@ Term.name blk) fn));
  insert_bb Graphs.Tid.start (Llvm.entry_block fn);
  return ()

let create_sub stack_ptr sub =
  let open Reader in
  if is_empty sub then (
    Format.eprintf "Skipping sub %s, has no blks\n" (Term.name sub);
    return ())
  else
    let* llvm_ctx, llvm_module = read () in
    (* Printf.eprintf "Converting sub %s\n" (Term.name sub); *)
    let blks = Term.enum blk_t sub in
    let fn =
      Llvm.lookup_function (sanitize_name @@ Term.name sub) llvm_module
      |> Base.Option.value_exn ~message:"create sub : function not found"
    in
    let llvm_builder = Llvm.builder_at_end llvm_ctx (Llvm.entry_block fn) in
    setup_llvars llvm_builder stack_ptr fn ()
    >>= initialize_bbs blks fn
    >>= build_entry_block llvm_builder sub
    >>= populate_blks blks sub >>= update_phis blks sub

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

let create_prog prog stack_ptr =
  Reader.Seq.iter ~f:(create_sub stack_ptr) (Term.enum sub_t prog)
