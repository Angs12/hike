open Bap.Std
open X86Regs
open Bap_main
open Bap.Std.Bil.Types
open Regular.Std
open Reachable_funcs
open Format
module StrMap = Map.Make (String)
module ExpMap = Map.Make (Exp)
module Libcmap = Map.Make (String)

let subs = ref StrMap.empty

let get_global_memory proj =
  let m = Project.memory proj in
  let lenght =
    Word.( - )
      (Base.Option.value_exn (Memmap.max_addr m))
      (Base.Option.value_exn (Memmap.min_addr m))
    |> Word.to_int_exn
  in
  let memory = Base.Array.init (lenght + 1) ~f:(fun _ -> 0) in
  Project.memory proj |> Memmap.to_sequence
  |> Seq.iter ~f:(fun (mem, _) ->
      Memory.iteri ~word_size:`r8 mem ~f:(fun index v ->
          memory.(Word.to_int_exn index) <- Word.to_int_exn v));
  memory

let set_sub sub =
  if Sub.name sub = "main" then
    subs :=
      StrMap.add "main"
        (Seq.singleton (Arg.create ~intent:Out !ret_reg (Var !ret_reg)))
        !subs
  else subs := StrMap.add (Term.tid sub |> Tid.name) Seq.empty !subs

let set_libc libc =
  Libcmap.iter
    (fun key (data : Decl_parser.funcdef) ->
      let ret = Gnu64_abi.return_regs data.return in
      let args = Gnu64_abi.arg_regs data.args in
      let func_decl =
        Seq.of_list
          (List.map (fun r -> Arg.create ~intent:Out r (Var r)) ret
          @ List.map (fun (r, i) -> Arg.create ~intent:i r (Var r)) args)
      in
      subs := StrMap.add ("@" ^ key) func_decl !subs)
    libc

let some_exn option =
  match option with Some x -> x | None -> failwith "some_exn"

let is_trivial exp = match exp with Int _ -> true | Var _ -> true | _ -> false

let pp_label tid =
  let sub =
    String.map (fun c ->
        if c = '#' then '_'
        else if c = '.' then '_'
        else if c = '%' then '_'
        else if c = '@' then '_'
        else c)
  in
  "blk_" ^ sub (Tid.name tid)

let pp_tid ?(prefix = "") ?(suffix = "") tid =
  let sub =
    String.map (fun c ->
        if c = '#' then '_'
        else if c = '.' then '_'
        else if c = '%' then '_'
        else if c = '@' then '_'
        else c)
  in
  sprintf "%%%s%s%s" prefix (sub (Tid.name tid)) suffix

let create_var ~is_virtual ~name ~typ ~tid =
  let sub =
    String.map (fun c ->
        if c = '#' then '_'
        else if c = '.' then '_'
        else if c = '%' then '_'
        else if c = '@' then '_'
        else c)
  in
  Var.create ~is_virtual (sub name ^ "_" ^ sub (Tid.name tid)) typ

let create_reg ~name ~typ ~tid = create_var ~is_virtual:false ~name ~typ ~tid
let create_virtual ~name ~typ ~tid = create_var ~is_virtual:true ~name ~typ ~tid

let pp_mem_type mem =
  match mem with
  | Var v -> (
      match Var.typ v with
      | Mem _ ->
          if Var.name v = "stack" then "ptr addrspace(0)"
          else if Var.name v = "cpu" then "ptr addrspace(1)"
          else "ptr addrspace(2)"
      | _ -> failwith "pp mem type: non-mem var")
  | _ -> failwith "pp mem type: non-var expression"

let pp_trivial_exp exp =
  let sub =
    String.map (fun c ->
        if c = '#' then '_'
        else if c = '.' then '_'
        else if c = '%' then '_'
        else c)
  in
  match exp with
  | Int i -> Int64.to_string (Word.to_int64_exn i)
  | Var v -> (
      match Var.typ v with
      | Imm _ | Unk -> sprintf "%%var_%s" (sub (Var.name v))
      | Mem _ ->
          if Var.name v = "stack" then "@stack"
          else if Var.name v = "cpu" then "@cpu"
          else sprintf "%%%s" (sub (Var.name v)))
  | _ -> failwith "pp exp: non-trivial expression"

let binop_str op =
  match op with
  | PLUS -> "add"
  | MINUS -> "sub"
  | TIMES -> "mul"
  | DIVIDE -> "udiv"
  | SDIVIDE -> "sdiv"
  | MOD -> "urem"
  | SMOD -> "srem"
  | AND -> "and"
  | OR -> "or"
  | XOR -> "xor"
  | LSHIFT -> "shl"
  | RSHIFT -> "lshr"
  | ARSHIFT -> "ashr"
  | EQ -> "icmp eq"
  | NEQ -> "icmp ne"
  | LT -> "icmp ult"
  | SLT -> "icmp slt"
  | LE -> "icmp ule"
  | SLE -> "icmp sle"

let var_type var =
  match Var.typ var with
  | Imm n -> sprintf "i%d" n
  | Mem (_, size) -> sprintf "i%d" (Size.in_bits size)
  | Unk -> "unk"

let var_size var =
  match Var.typ var with Imm n -> n | _ -> failwith "pp exp type: non-imm var"

let pp_ret ppf args =
  let ret_type = ref "void" in
  Seq.iter args ~f:(fun arg ->
      match Arg.intent arg with
      | Some i -> (
          match i with
          | In -> ()
          | Out -> ret_type := var_type !ret_reg
          | Both -> ())
      | None -> ());
  fprintf ppf "%s" !ret_type

let is_mem var = match Var.typ var with Mem _ -> true | _ -> false
let word_type word = sprintf "i%d" (Word.bitwidth word)

let trivial_exp_name exp =
  match exp with
  | Var v -> Var.name v
  | _ -> failwith "pp exp name: non-trivial expression"

let trivial_exp_type exp =
  match exp with
  | Int i -> word_type i
  | Var v -> var_type v
  | _ -> failwith "pp exp type: non-trivial expression"

let pp_type exp1 exp2 =
  if trivial_exp_type exp1 > trivial_exp_type exp2 then trivial_exp_type exp1
  else trivial_exp_type exp2

let pp_binop (op, e1, e2) =
  if is_trivial e1 && is_trivial e2 then
    sprintf "%s %s %s, %s" (binop_str op) (pp_type e1 e2) (pp_trivial_exp e1)
      (pp_trivial_exp e2)
  else failwith "pp binop: non-trivial definition"

let all_ones exp =
  match exp with
  | Int i -> Word.ones @@ Word.bitwidth i |> Word.signed |> Word.to_int_exn
  | Var v -> (
      match Var.typ v with
      | Imm n -> Word.ones n |> Word.signed |> Word.to_int_exn
      | _ -> failwith "pp all ones: non-imm var")
  | _ -> failwith "pp all ones: non-trivial expression"

let pp_unop (op, e) =
  if is_trivial e then
    match op with
    | NEG -> sprintf "sub %s 0, %s" (trivial_exp_type e) (pp_trivial_exp e)
    | NOT ->
        sprintf "xor %s %d, %s" (trivial_exp_type e) (all_ones e)
          (pp_trivial_exp e)
  else failwith "pp unop: non-trivial definition"

let size_type size = sprintf "i%d" (Size.in_bits size)

let exp_type_size exp =
  match exp with
  | Int i -> Word.bitwidth i
  | Var v -> (
      match Var.typ v with
      | Imm n -> n
      | _ -> failwith "pp exp type: non-imm var")
  | _ -> failwith "pp exp type: non-trivial expression"

let pp_exp ppf exp =
  match exp with
  | BinOp (op, e1, e2) -> fprintf ppf "%s" (pp_binop (op, e1, e2))
  | UnOp (op, e) -> fprintf ppf "%s" (pp_unop (op, e))
  | Var v ->
      let t = var_type v in
      pp_trivial_exp exp |> fprintf ppf "add %s %s, 0" t
  | Int _ ->
      let t = trivial_exp_type exp in
      pp_trivial_exp exp |> fprintf ppf "add %s %s, 0" t
  | Cast (cast, i, exp) -> (
      match cast with
      | UNSIGNED ->
          fprintf ppf "zext %s %s to i%d" (trivial_exp_type exp)
            (pp_trivial_exp exp) i
      | SIGNED ->
          fprintf ppf "sext %s %s to i%d" (trivial_exp_type exp)
            (pp_trivial_exp exp) i
      | LOW ->
          fprintf ppf "trunc %s %s to i%d" (trivial_exp_type exp)
            (pp_trivial_exp exp) i
      | _ -> failwith "pp exp cast high: non-trivial expression")
  | _ -> fprintf ppf "pp_expr: Not trivial expression\n"

let label_tid label =
  match label with
  | Direct tid -> tid
  | Indirect _ -> failwith "label_tid: indirect label"

let ret_arg args =
  Seq.exists args ~f:(fun arg ->
      match Arg.intent arg with Some Out -> true | _ -> false)

let ready_args ppf tid args =
  Seq.iter args ~f:(fun arg ->
      match Arg.intent arg with
      | Some i -> (
          match i with
          | In -> ()
          | Out -> ()
          | Both ->
              let var = Arg.lhs arg in
              let reg =
                create_reg ~name:("reg_" ^ Var.name var) ~tid ~typ:(Var.typ var)
              in
              let tmp =
                create_reg ~name:("tmp_" ^ Var.name var) ~tid ~typ:(Var.typ var)
              in
              let ptr =
                create_reg ~name:("ptr_" ^ Var.name var) ~tid ~typ:(Var.typ var)
              in
              fprintf ppf "\t%s = ptrtoint ptr addrspace(0) @stack to i64\n"
                (pp_trivial_exp (Var tmp));
              fprintf ppf "\t%s = add %s %s, %s\n" (pp_trivial_exp (Var ptr))
                (trivial_exp_type (Var tmp))
                (pp_trivial_exp (Var tmp)) (pp_trivial_exp (Var reg)))
      | None -> ())

let pp_call_args tid args =
  let args =
    Seq.fold args ~init:"" ~f:(fun prev arg ->
        let var = Arg.lhs arg in
        match Arg.intent arg with
        | Some i -> (
            match i with
            | In ->
                let var =
                  create_reg
                    ~name:("reg_" ^ Var.name var)
                    ~tid ~typ:(Var.typ var)
                in

                sprintf "%s %s %s," prev (var_type var)
                  (pp_trivial_exp (Var var))
            | Out -> prev
            | Both ->
                let var =
                  create_reg
                    ~name:("ptr_" ^ Var.name var)
                    ~tid ~typ:(Var.typ var)
                in
                sprintf "%s %s %s," prev
                  (trivial_exp_type (Var var))
                  (pp_trivial_exp (Var var)))
        | None -> prev)
  in
  if args = "" then "" else String.sub args 0 (String.length args - 1)

let pp_concat ppf (var, exp1, exp2) =
  let temp_var1 = pp_trivial_exp (Var var) ^ "_tmp1" in
  let temp_var2 = pp_trivial_exp (Var var) ^ "_tmp2" in
  let temp_var3 = pp_trivial_exp (Var var) ^ "_tmp3" in
  fprintf ppf "\t%s = zext %s %s to %s\n" temp_var1 (trivial_exp_type exp1)
    (pp_trivial_exp exp1) (var_type var);
  fprintf ppf "\t%s = shl %s %s, %d\n" temp_var2 (var_type var) temp_var1
    (exp_type_size exp2);
  fprintf ppf "\t%s = zext %s %s to %s\n" temp_var3 (trivial_exp_type exp2)
    (pp_trivial_exp exp2) (var_type var);
  fprintf ppf "\t%s = and %s %s, %s\n" (pp_trivial_exp (Var var)) (var_type var)
    temp_var2 temp_var3

let pp_extract ppf (var, hi, lo, exp) =
  let temp_var = pp_trivial_exp (Var var) ^ "_tmp" in
  fprintf ppf "\t%s = lshr %s %s, %d\n" temp_var (trivial_exp_type exp)
    (pp_trivial_exp exp) lo;
  let result_size = hi - lo + 1 in
  fprintf ppf "\t%s = trunc %s %s to i%d\n" (pp_trivial_exp (Var var))
    (trivial_exp_type exp) temp_var result_size

let pp_load ppf (var, mem, addr, size) =
  let size_type = size_type size in
  let temp_var = pp_trivial_exp (Var var) ^ "_tmp" in
  fprintf ppf "\t%s = getelementptr %s, %s %s, %s %s\n" temp_var
    (trivial_exp_type mem) (pp_mem_type mem) (pp_trivial_exp mem)
    (trivial_exp_type addr) (pp_trivial_exp addr);
  fprintf ppf "\t%s = load %s, %s %s\n" (pp_trivial_exp (Var var)) size_type
    (pp_mem_type mem) temp_var

let pp_store ppf (tid, mem, addr, data) =
  let temp_var = pp_tid ~suffix:"_tmp" tid in
  fprintf ppf "\t%s = getelementptr %s, %s %s, %s %s\n" temp_var
    (trivial_exp_type mem) (pp_mem_type mem) (pp_trivial_exp mem)
    (trivial_exp_type addr) (pp_trivial_exp addr);
  fprintf ppf "\tstore %s %s, %s %s\n" (trivial_exp_type data)
    (pp_trivial_exp data) (pp_mem_type mem) temp_var

let pp_cond ppf cond tid =
  match cond with
  | Int i ->
      fprintf ppf "\t%s = add i1 %s , 0\n" (pp_tid tid)
        (Int64.to_string (Word.to_int64_exn i))
  | Var _ -> fprintf ppf "\t%s = %a\n" (pp_tid tid) pp_exp cond
  | _ -> failwith "pp cond: non-trivial expression"

let pp_func tid =
  let sub =
    String.map (fun c ->
        if c = '#' then '_'
        else if c = '.' then '_'
        else if c = '%' then '_'
        else c)
  in
  sprintf "%s" (sub (Tid.name tid))

let goto_label_exn jmp =
  match jmp with Goto l -> l | _ -> failwith "goto_label_exn: ret jmp"

let pp_branches ppf branches =
  if Seq.length branches = 1 then
    let br = Seq.hd_exn branches in
    let jmp_target = Jmp.kind br |> goto_label_exn |> label_tid in
    fprintf ppf "\tbr label %%%s\n" (pp_label jmp_target)
  else if Seq.length branches = 2 then (
    let br1 = Seq.hd_exn branches in
    let else_jmp = Seq.to_list branches |> Base.List.last_exn in
    let jmp_target = Jmp.kind br1 |> goto_label_exn |> label_tid in
    let else_target = Jmp.kind else_jmp |> goto_label_exn |> label_tid in
    let cond = Jmp.cond br1 in
    let cond_var =
      create_virtual ~name:"cond" ~tid:(Term.tid br1) ~typ:(Imm 1)
    in
    fprintf ppf "\t%s = %a\n" (pp_trivial_exp (Var cond_var)) pp_exp cond;
    fprintf ppf "\tbr i1 %s, label %%%s, label %%%s\n"
      (pp_trivial_exp (Var cond_var))
      (pp_label jmp_target) (pp_label else_target))
  else failwith "pp_branches: more than 2 branches"

let pp_return tid return_reg ppf _ =
  match return_reg with
  | None -> ()
  | Some return_reg ->
      let res =
        create_reg
          ~name:("res_" ^ Var.name !ret_reg)
          ~tid
          ~typ:(Var.typ (Arg.lhs return_reg))
      in
      let new_ret =
        create_reg
          ~name:("reg_" ^ Var.name !ret_reg)
          ~tid ~typ:(Var.typ !ret_reg)
      in
      fprintf ppf "\t%s = %a\n" (pp_trivial_exp (Var res)) pp_exp
        (Exp.substitute (Var !ret_reg) (Var new_ret) (Arg.rhs return_reg))

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
          | Direct tid ->
              let args =
                Base.Option.value_exn
                  ~message:(sprintf "cf_type: sub %s not found" (Tid.name tid))
                  (StrMap.find_opt (Tid.name tid) !subs)
              in
              let ret = ret_arg args in
              fprintf err_formatter "%s -- %b \n" (Tid.name tid) ret;
              if ret then Call else CallVoid
          | Indirect _ -> Call)
      | None -> CallRet)
  | Int _ -> Int

let pp_cast (var, cast, i, exp) =
  let var_name = pp_trivial_exp (Var var) in
  match cast with
  | UNSIGNED ->
      sprintf "%s = zext %s %s to i%d" var_name (trivial_exp_type exp)
        (pp_trivial_exp exp) i
  | SIGNED ->
      sprintf "%s = sext %s %s to i%d" var_name (trivial_exp_type exp)
        (pp_trivial_exp exp) i
  | HIGH ->
      sprintf "%s_tmp = lshr %s %s, %d" var_name (trivial_exp_type exp)
        (pp_trivial_exp exp)
        (exp_type_size exp - i)
      ^ "\n\t"
      ^ sprintf "%s = trunc %s %s_tmp to i%d" var_name (trivial_exp_type exp)
          var_name i
  | LOW ->
      sprintf "%s = trunc %s %s to i%d" var_name (trivial_exp_type exp)
        (pp_trivial_exp exp) i

let pp_def ppf def =
  let var = Def.lhs def in
  let var_name = pp_trivial_exp (Var var) in
  let expr = Def.rhs def in
  match expr with
  | BinOp (op, e1, e2) ->
      pp_binop (op, e1, e2) |> fprintf ppf "\t%s = %s \n" var_name
  | UnOp (op, e) -> pp_unop (op, e) |> fprintf ppf "\t%s = %s \n" var_name
  | Cast (cast, i, exp) -> pp_cast (var, cast, i, exp) |> fprintf ppf "\t%s \n"
  | Load (mem, addr, _, size) -> pp_load ppf (var, mem, addr, size)
  | Concat (exp1, exp2) -> pp_concat ppf (var, exp1, exp2)
  | Extract (hi, lo, exp) -> pp_extract ppf (var, hi, lo, exp)
  | Var _ ->
      if is_mem var then ()
      else
        let t = var_type var in
        pp_trivial_exp expr |> fprintf ppf "\t%s = add %s %s, 0 \n" var_name t
  | Int _ ->
      pp_trivial_exp expr
      |> fprintf ppf "\t%s = add %s %s, 0 \n" var_name (var_type var)
  | Store (mem, addr, data, _, _) -> pp_store ppf (Term.tid def, mem, addr, data)
  | Unknown _ -> ()
  | _ ->
      fprintf ppf "Not trivial expression\n";
      pp_trivial_exp expr |> fprintf ppf "\t%s = %s \n" var_name

let pp_func_call blk_tid ret_var fallthrough target ppf =
  let args =
    Base.Option.value_exn ~message:"pp_func_call: sub not found"
      (StrMap.find_opt (Tid.name target) !subs)
  in
  Seq.iter args ~f:(fun arg -> fprintf err_formatter "%s\n" (Arg.str () arg));
  let ret = ret_arg args in
  match ret with
  | true ->
      ready_args ppf blk_tid args;
      fprintf ppf "\t%s = call zeroext %s %s(%s)\n"
        (pp_trivial_exp (Var ret_var))
        (var_type ret_var) (pp_func target)
        (pp_call_args blk_tid args);
      let store_exp = set_reg !ret_reg (Var ret_var) in
      let store_def = Def.create cpu_regs store_exp in
      pp_def ppf store_def;
      fprintf ppf "\tbr label %%%s\n" (pp_label fallthrough)
  | false ->
      ready_args ppf blk_tid args;
      fprintf ppf "\tcall %s %s(%s)\n" "void" (pp_func target)
        (pp_call_args blk_tid args);
      fprintf ppf "\tbr label %%%s\n" (pp_label fallthrough)

let pp_call tid returns_value ret ppf call =
  match (Call.return call, Call.target call) with
  | None, _ -> (
      match returns_value with
      | true ->
          fprintf ppf "\tret %s %s\n" (var_type ret) (pp_trivial_exp (Var ret))
      | false -> fprintf ppf "\tret void\n")
  | Some (Direct ret_label), Direct target_label ->
      pp_func_call tid ret ret_label target_label ppf
  | _, _ -> fprintf ppf "\tCALL\n"

let pp_phi ppf phi =
  let var = Phi.lhs phi in
  if is_mem var || Base.List.mem !regs var ~equal:Var.same then ()
  else
    let var_name = pp_trivial_exp (Var var) in
    let vals = Phi.values phi in
    let values =
      Seq.fold vals ~init:"" ~f:(fun prev (tid, exp) ->
          sprintf "%s [%s,%%%s]," prev (pp_trivial_exp exp) (pp_label tid))
    in
    let values = String.sub values 0 (String.length values - 1) in
    fprintf ppf "\t%s = phi %s %s\n" var_name
      (trivial_exp_type (Var var))
      values

let call_exn jmp =
  match Jmp.kind jmp with Call j -> j | _ -> failwith "call_exn:"

let has_var var exp =
  (object
     inherit [bool] Exp.visitor
     method! enter_var v flag = if Var.same v var || flag then true else false
  end)
    #visit_exp
    exp false

let base_exp_sub base_var sub =
  object
    inherit Exp.mapper
    method! map_var var = if Var.same var base_var then Var sub else Var var
  end

let pp_elts returns_value blk ppf elts =
  let control_flow = Term.enum jmp_t blk in
  let tid = Term.tid blk in
  Seq.iter elts ~f:(function
    | `Phi phi -> fprintf ppf "%a" pp_phi phi
    | `Def def -> fprintf ppf "%a" pp_def def
    | _ -> ());
  match cf_type control_flow with
  | Br -> pp_branches ppf control_flow
  | Ret -> failwith "pp_elts: RET not implemented"
  | Int -> failwith "pp_elts: INT not implemented"
  | Call | CallVoid | CallRet ->
      let call = Seq.hd_exn control_flow |> call_exn in
      let res =
        create_reg
          ~name:("reg_" ^ Var.name !ret_reg)
          ~tid ~typ:(Var.typ !ret_reg)
      in
      pp_call tid returns_value res ppf call

let pp_args args =
  let args =
    Seq.fold args ~init:"" ~f:(fun prev arg ->
        let var = Arg.lhs arg in
        match Arg.intent arg with
        | Some i -> (
            match i with
            | In ->
                sprintf "%s %s %s," prev (var_type var)
                  (pp_trivial_exp (Var var))
            | Out -> prev
            | Both ->
                sprintf "%s %s %s," prev (pp_mem_type (Var var))
                  (pp_trivial_exp (Var var)))
        | None -> prev)
  in
  if args = "" then "" else String.sub args 0 (String.length args - 1)
(* remove last comma *)

let update_args sub =
  let builder =
    Sub.Builder.create ~tid:(Term.tid sub) ~name:(Sub.name sub) ()
  in
  Seq.iter (Term.enum blk_t sub) ~f:(fun blk -> Sub.Builder.add_blk builder blk);
  Sub.Builder.result builder

let pp_body ret ppf =
  Seq.iter ~f:(fun blk ->
      fprintf ppf "\n%s:\n%a\n"
        (pp_label (Term.tid blk))
        (pp_elts ret blk) (Blk.elts blk))

let entry_blk_tid sub =
  let blks = Term.enum blk_t sub in
  Term.tid (Seq.hd_exn blks)

let update_stack sub =
  Term.map blk_t sub ~f:(fun blk ->
      let builder =
        Blk.Builder.init ~same_tid:true ~copy_phis:true ~copy_jmps:true blk
      in
      Seq.iter (Term.enum def_t blk) ~f:(fun def ->
          let e = Def.rhs def in
          let e = Exp.map (base_exp_sub !mem !stack) e in
          Blk.Builder.add_def builder (Def.with_rhs def e));
      Blk.Builder.result builder)

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
                  (Jmp.create_ret (Indirect (Var (Var.create "ret" (Imm 64)))));
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

let update_main lenght sub =
  if Sub.name sub = "main" then (
    let entry_tid =
      Base.Option.value_exn ~message:"Main function has no blocks"
        (Sub.to_graph sub |> Graphs.Tid.Node.succs Graphs.Tid.start |> Seq.hd)
    in
    let reg = !sp in
    let sub =
      Term.map blk_t sub ~f:(fun blk ->
          if Term.tid blk = entry_tid then (
            let builder =
              Blk.Builder.init ~copy_phis:true ~copy_jmps:true blk
            in
            (let data =
               Bil.Int (Word.of_int ~width:(var_size reg) (lenght - 1))
             in
             let def = Def.create reg (set_reg reg data) in
             Blk.Builder.add_def builder def);
            Term.enum def_t blk
            |> Seq.iter ~f:(fun def -> Blk.Builder.add_def builder def);
            Blk.Builder.result builder)
          else blk)
    in
    let sub_builder =
      Sub.Builder.create ~tid:(Term.tid sub) ~name:(Sub.name sub) ()
    in
    Seq.iter (Term.enum blk_t sub) ~f:(fun blk ->
        Sub.Builder.add_blk sub_builder blk);
    Sub.Builder.add_arg sub_builder
      (Arg.create ~intent:Out !ret_reg (Var !ret_reg));
    Sub.Builder.result sub_builder)
  else sub

let transfer_regs sub =
  Term.map blk_t sub ~f:(fun blk ->
      let tid = Term.tid blk in
      let reg_map = ref Var.Map.empty in
      let ret_reg_var =
        create_reg ~name:(Var.name !ret_reg) ~tid ~typ:(Var.typ !ret_reg)
      in
      reg_map := Var.Map.add_exn !reg_map ~key:!ret_reg ~data:ret_reg_var;
      let blk =
        Base.List.fold ~init:blk !regs ~f:(fun blk base ->
            let ver = ref 0 in
            let reg =
              create_reg ~name:(Var.name base) ~tid ~typ:(Var.typ base)
            in
            Blk.map_elts blk ~def:(fun def ->
                let var = Def.lhs def in
                let exp = Def.rhs def in
                if has_var base exp && not (Var.Map.mem !reg_map base) then
                  reg_map := Var.Map.add_exn !reg_map ~key:base ~data:reg
                else ();
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
      Var.Map.iteri !reg_map ~f:(fun ~key ~data:_ ->
          let var = create_reg ~name:(Var.name key) ~tid ~typ:(Var.typ key) in
          let def = Def.create var (get_reg key) in
          Blk.Builder.add_def builder def);
      Blk.elts blk
      |> Seq.iter ~f:(fun elt ->
          match elt with `Def def -> Blk.Builder.add_def builder def | _ -> ());
      Var.Map.iteri !reg_map ~f:(fun ~key ~data ->
          match (cf_type (Term.enum jmp_t blk), Var.same key !ret_reg) with
          | Call, true -> ()
          | _, _ ->
              let reg_var =
                create_reg ~name:("reg_" ^ Var.name key) ~tid ~typ:(Var.typ key)
              in
              let def = Def.create reg_var (Var data) in
              let store_def = Def.create cpu_regs (set_reg key (Var reg_var)) in
              Blk.Builder.add_def builder def;
              Blk.Builder.add_def builder store_def);
      Blk.Builder.result builder)

let pp_sub ppf sub =
  let args = Term.enum arg_t sub in
  let blks = Term.enum blk_t sub in
  let ret = ret_arg args in
  fprintf ppf "@[<2>define %a %s(%s) {@\n%a@]@\n}" pp_ret args
    (pp_func @@ Term.tid sub)
    (pp_args args) (pp_body ret) blks

let libc_calls libc sub =
  not
    (Libcmap.mem (Sub.name sub) libc
    || Base.String.is_substring ~substring:":external" (Sub.name sub))

let print_sections p =
  Project.memory p |> Memmap.to_sequence
  |> Seq.iter ~f:(fun (mem, x) ->
      Base.Option.iter (Value.get Image.section x) ~f:(fun name ->
          fprintf err_formatter "Section: %s@.%a@." name Memory.pp mem))

let pp_prog proj ppf prog =
  let target = Project.target proj in
  Program.pp err_formatter prog;
  print_sections proj;
  let mem = get_global_memory proj in
  for i = 8196 to 8204 do
    fprintf err_formatter "%c" (Char.chr mem.(i))
  done;
  let stack = Base.Array.init 1024 ~f:(fun _ -> 0) in
  let mem = Array.append mem stack in
  let data =
    Base.Array.fold ~init:"" ~f:(fun acc v -> acc ^ sprintf "i8 %d," v) mem
  in
  (* remove last comma *)
  let data =
    if data = "" then "" else String.sub data 0 (String.length data - 1)
  in
  let length = Array.length mem in
  let libc = Decl_parser.parse_header_file "stdio_headers.ll" in
  set_ret_reg target;
  set_regs target;
  set_stack target;
  set_sp target;
  set_mem target;
  set_libc libc;
  (* convert only functions that are reachable from main *)
  let main_sub =
    Term.enum sub_t prog |> Seq.find_exn ~f:(fun sub -> Sub.name sub = "main")
  in
  let reachable =
    reachable_funcs prog main_sub |> SubSet.filter (libc_calls libc)
  in
  SubSet.iter (fun sub -> fprintf err_formatter "%s" (Sub.name sub)) reachable;
  Program.pp err_formatter prog;
  SubSet.iter (fun sub -> set_sub sub) reachable;
  let updated_subs =
    SubSet.map
      (fun sub ->
        sub |> update_args |> update_rets |> Sub.ssa |> Sub.flatten
        |> update_stack |> transfer_regs |> update_main length)
      reachable
  in
  fprintf ppf "@cpu = addrspace(1) global [650 x i8]  zeroinitializer \n";
  fprintf ppf "@stack = addrspace(0) global [%d x i8] [ %s ]\n" length data;
  SubSet.iter (fprintf ppf "@[%a@]@\n" pp_sub) updated_subs

let pp ppf proj =
  let pass =
    Project.find_pass "trivial-condition-form" |> fun pass ->
    match pass with
    | Some pass -> pass
    | None -> failwith "pp: trivial-condition-form pass not found"
  in
  let open Result in
  let proj =
    match Project.Pass.run pass proj with
    | Ok p -> p
    | Error _ -> failwith "pp: pass failed"
  in
  fprintf ppf "@[%a@]" (pp_prog proj) (Project.program proj)

let main proj =
  let ppf = Format.std_formatter in
  pp ppf proj

let () =
  Extension.declare @@ fun _ctxt ->
  Project.register_pass' main;
  Ok ()
