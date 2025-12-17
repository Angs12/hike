open Bap.Std
open Bap_main
open Bap.Std.Bil.Types
open Bap_core_theory
open Regular.Std
open Theory.Role.Register
open Format
module StrMap = Map.Make (String)
module ExpMap = Map.Make (Exp)

let ret_reg = ref @@ Var.create "DUMMY" (Imm 1)

let set_ret_reg target =
  let abi = Theory.Target.abi target in
  if abi = Theory.Abi.gnu then ret_reg := Var.create "RAX" (Imm 64)
  else failwith "unsupported target"

let cpu_regs = Var.create "cpu" (Mem (`r32, Size.of_int_exn 8))
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
let regs = ref []
let subs = ref Tid.Map.empty

let set_sub sub =
  if Sub.name sub = "main" then
    subs :=
      Tid.Map.add_exn !subs ~key:(Term.tid sub)
        ~data:(Seq.singleton (Arg.create ~intent:Out !ret_reg (Var !ret_reg)))
  else subs := Tid.Map.add_exn !subs ~key:(Term.tid sub) ~data:Seq.empty

let set_sp target =
  sp :=
    Theory.Target.reg target stack_pointer
    |> Base.Option.value_exn ~message:"No stack pointer"
    |> Var.reify

let set_regs target =
  regs :=
    Theory.Target.regs target ~roles:[ general; integer ]
    |> Base.Set.to_list |> Base.List.map ~f:Var.reify

let set_stack target =
  let byte = Theory.Target.byte target in
  let bits =
    match Theory.Target.bits target with
    | 32 -> `r32
    | 64 -> `r64
    | _ -> failwith "stack: non-32 or 64 bits"
  in
  stack := Var.create "stack" (Mem (bits, Size.of_int_exn byte))

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

let create_arg ~name ~typ ~tid =
  create_var ~is_virtual:false ~name:("arg_" ^ name) ~typ ~tid

let create_local ~name ~typ ~tid =
  create_var ~is_virtual:false ~name:("local_" ^ name) ~typ ~tid

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
  if trivial_exp_type exp1 = trivial_exp_type exp2 then trivial_exp_type exp1
  else failwith "pp type: non-equal types"

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

let pp_call_args tid args =
  let args =
    Seq.fold args ~init:"" ~f:(fun prev arg ->
        let var = Arg.lhs arg in
        let var =
          create_reg ~name:("reg_" ^ Var.name var) ~tid ~typ:(Var.typ var)
        in
        match Arg.intent arg with
        | Some i -> (
            match i with
            | In ->
                sprintf "%s %s %s," prev (var_type var)
                  (pp_trivial_exp (Var var))
            | Out -> prev
            | Both ->
                sprintf "%s %s %s," prev (var_type var)
                  (pp_trivial_exp (Var var)))
        | None -> prev)
  in
  if args = "" then "" else String.sub args 0 (String.length args - 1)

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
                Tid.Map.find !subs tid
                |> Base.Option.value_exn ~message:"cf_type: sub not found"
              in
              let ret = ret_arg args in
              if ret then Call else CallVoid
          | Indirect _ -> Call)
      | None -> CallRet)
  | Int _ -> Int

let pp_func_call blk_tid ret_var fallthrough target ppf =
  let args =
    Tid.Map.find !subs target
    |> Base.Option.value_exn ~message:"pp_func_call: sub not found"
  in
  let ret = ret_arg args in
  match ret with
  | true ->
      fprintf ppf "\t%s = call zeroext %s %s(%s)\n"
        (pp_trivial_exp (Var ret_var))
        (var_type ret_var) (pp_func target)
        (pp_call_args blk_tid args);
      fprintf ppf "\tbr label %%%s\n" (pp_label fallthrough)
  | false ->
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
  | Concat _ -> fprintf ppf "CONCAT"
  | Extract _ -> fprintf ppf "EXTRACT"
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

let call_exn jmp =
  match Jmp.kind jmp with Call j -> j | _ -> failwith "call_exn:"

let base_exp_sub base_var sub =
  object
    inherit Exp.mapper as super
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

let word_exp n = Bil.Int (Word.of_int ~width:32 n)

let get_reg reg =
  if Var.name reg = "CS" then
    Load (Var cpu_regs, word_exp 0, BigEndian, Size.r16)
  else if Var.name reg = "DS" then
    Load (Var cpu_regs, word_exp 2, BigEndian, Size.r16)
  else if Var.name reg = "ES" then
    Load (Var cpu_regs, word_exp 4, BigEndian, Size.r16)
  else if Var.name reg = "R10" then
    Load (Var cpu_regs, word_exp 6, BigEndian, Size.r64)
  else if Var.name reg = "R11" then
    Load (Var cpu_regs, word_exp 14, BigEndian, Size.r64)
  else if Var.name reg = "R12" then
    Load (Var cpu_regs, word_exp 22, BigEndian, Size.r64)
  else if Var.name reg = "R13" then
    Load (Var cpu_regs, word_exp 30, BigEndian, Size.r64)
  else if Var.name reg = "R14" then
    Load (Var cpu_regs, word_exp 38, BigEndian, Size.r64)
  else if Var.name reg = "R15" then
    Load (Var cpu_regs, word_exp 46, BigEndian, Size.r64)
  else if Var.name reg = "R8" then
    Load (Var cpu_regs, word_exp 54, BigEndian, Size.r64)
  else if Var.name reg = "R9" then
    Load (Var cpu_regs, word_exp 62, BigEndian, Size.r64)
  else if Var.name reg = "RAX" then
    Load (Var cpu_regs, word_exp 70, BigEndian, Size.r64)
  else if Var.name reg = "RBP" then
    Load (Var cpu_regs, word_exp 78, BigEndian, Size.r64)
  else if Var.name reg = "RBX" then
    Load (Var cpu_regs, word_exp 86, BigEndian, Size.r64)
  else if Var.name reg = "RCX" then
    Load (Var cpu_regs, word_exp 94, BigEndian, Size.r64)
  else if Var.name reg = "RDI" then
    Load (Var cpu_regs, word_exp 102, BigEndian, Size.r64)
  else if Var.name reg = "RDX" then
    Load (Var cpu_regs, word_exp 110, BigEndian, Size.r64)
  else if Var.name reg = "RSI" then
    Load (Var cpu_regs, word_exp 118, BigEndian, Size.r64)
  else if Var.name reg = "RSP" then
    Load (Var cpu_regs, word_exp 126, BigEndian, Size.r64)
  else if Var.name reg = "SS" then
    Load (Var cpu_regs, word_exp 134, BigEndian, Size.r16)
  else failwith "get_reg: not implemented"

let set_reg reg data =
  if Var.name reg = "CS" then
    Store (Var cpu_regs, word_exp 0, data, BigEndian, Size.r16)
  else if Var.name reg = "DS" then
    Store (Var cpu_regs, word_exp 2, data, BigEndian, Size.r16)
  else if Var.name reg = "ES" then
    Store (Var cpu_regs, word_exp 4, data, BigEndian, Size.r16)
  else if Var.name reg = "R10" then
    Store (Var cpu_regs, word_exp 6, data, BigEndian, Size.r64)
  else if Var.name reg = "R11" then
    Store (Var cpu_regs, word_exp 14, data, BigEndian, Size.r64)
  else if Var.name reg = "R12" then
    Store (Var cpu_regs, word_exp 22, data, BigEndian, Size.r64)
  else if Var.name reg = "R13" then
    Store (Var cpu_regs, word_exp 30, data, BigEndian, Size.r64)
  else if Var.name reg = "R14" then
    Store (Var cpu_regs, word_exp 38, data, BigEndian, Size.r64)
  else if Var.name reg = "R15" then
    Store (Var cpu_regs, word_exp 46, data, BigEndian, Size.r64)
  else if Var.name reg = "R8" then
    Store (Var cpu_regs, word_exp 54, data, BigEndian, Size.r64)
  else if Var.name reg = "R9" then
    Store (Var cpu_regs, word_exp 62, data, BigEndian, Size.r64)
  else if Var.name reg = "RAX" then
    Store (Var cpu_regs, word_exp 70, data, BigEndian, Size.r64)
  else if Var.name reg = "RBP" then
    Store (Var cpu_regs, word_exp 78, data, BigEndian, Size.r64)
  else if Var.name reg = "RBX" then
    Store (Var cpu_regs, word_exp 86, data, BigEndian, Size.r64)
  else if Var.name reg = "RCX" then
    Store (Var cpu_regs, word_exp 94, data, BigEndian, Size.r64)
  else if Var.name reg = "RDI" then
    Store (Var cpu_regs, word_exp 102, data, BigEndian, Size.r64)
  else if Var.name reg = "RDX" then
    Store (Var cpu_regs, word_exp 110, data, BigEndian, Size.r64)
  else if Var.name reg = "RSI" then
    Store (Var cpu_regs, word_exp 118, data, BigEndian, Size.r64)
  else if Var.name reg = "RSP" then
    Store (Var cpu_regs, word_exp 126, data, BigEndian, Size.r64)
  else if Var.name reg = "SS" then
    Store (Var cpu_regs, word_exp 134, data, BigEndian, Size.r16)
  else failwith "set_reg: not implemented"

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
              Term.first jmp_t blk
              |> Base.Option.value_exn ~message:"ret jmp not found"
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

let update_main sub =
  if Sub.name sub = "main" then (
    let entry_tid =
      Sub.to_graph sub
      |> Graphs.Tid.Node.succs Graphs.Tid.start
      |> Seq.hd
      |> Base.Option.value_exn ~message:"Main function has no blocks"
    in
    let sub =
      Term.map blk_t sub ~f:(fun blk ->
          if Term.tid blk = entry_tid then (
            let builder =
              Blk.Builder.init ~copy_phis:true ~copy_jmps:true blk
            in
            Base.List.iter !regs ~f:(fun reg ->
                let data =
                  if Var.same reg !sp then
                    Bil.Int (Word.of_int ~width:(var_size reg) 65535)
                  else Bil.Int (Word.zero (var_size reg))
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
      let tmp_reg_map =
        !regs
        |> Base.List.fold ~init:Var.Map.empty ~f:(fun reg_map v ->
               Var.Map.add_exn reg_map ~key:v
                 ~data:(create_reg ~name:(Var.name v) ~tid ~typ:(Var.typ v)))
      in
      let reg_map = ref tmp_reg_map in
      let blk =
        Var.Map.fold ~init:blk tmp_reg_map ~f:(fun ~key:base ~data:reg blk ->
            let ver = ref 0 in
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
      (* let graph = Sub.to_cfg sub in *)
      (* let node = Graphs.Ir.Node.create blk in *)
      (* let inputs = *)
      (*   Graphs.Ir.Node.inputs node graph *)
      (*   |> Seq.map ~f:Graphs.Ir.Edge.src *)
      (*   |> Seq.map ~f:Graphs.Ir.Node.label *)
      (*   |> Seq.map ~f:Term.tid *)
      (* in *)
      (* if Seq.is_empty inputs then *)
      Var.Map.iteri !reg_map ~f:(fun ~key ~data:_ ->
          let var = create_reg ~name:(Var.name key) ~tid ~typ:(Var.typ key) in
          let def = Def.create var (get_reg key) in
          Blk.Builder.add_def builder def);
      (* else *)
      (*   Var.Map.iteri !reg_map ~f:(fun ~key ~data:_ -> *)
      (*       let var = create_reg ~name:(Var.name key) ~tid ~typ:(Var.typ key) in *)
      (*       let vals = *)
      (*         Seq.fold inputs ~init:[] ~f:(fun vals tid -> *)
      (*             let reg_var = *)
      (*               create_reg *)
      (*                 ~name:("reg_" ^ Var.name key) *)
      (*                 ~tid ~typ:(Var.typ key) *)
      (*             in *)
      (*             (tid, Var reg_var) :: vals) *)
      (*       in *)
      (*       let phi = Phi.of_list var vals in *)
      (*       Blk.Builder.add_phi builder phi) *)
      Blk.elts blk
      |> Seq.iter ~f:(fun elt ->
             match elt with
             | `Def def -> Blk.Builder.add_def builder def
             | _ -> ());
      Var.Map.iteri !reg_map ~f:(fun ~key ~data ->
          match (cf_type (Term.enum jmp_t blk), Var.same key !ret_reg) with
          | Call, true -> ()
          | _, _ ->
              let reg_var =
                create_reg ~name:("reg_" ^ Var.name key) ~tid ~typ:(Var.typ key)
              in
              let def = Def.create reg_var (Var data) in
              Blk.Builder.add_def builder def);
      (match cf_type (Term.enum jmp_t blk) with
      | Call | Ret | CallVoid | CallRet ->
          Var.Map.iteri !reg_map ~f:(fun ~key ~data:_ ->
              let reg_var =
                create_reg ~name:("reg_" ^ Var.name key) ~tid ~typ:(Var.typ key)
              in
              let store_def = Def.create cpu_regs (set_reg key (Var reg_var)) in
              Blk.Builder.add_def builder store_def)
      | _ -> ());
      Blk.Builder.result builder)

let pp_sub ppf sub =
  let args = Term.enum arg_t sub in
  let blks = Term.enum blk_t sub in
  let ret = ret_arg args in
  fprintf ppf "@[<2>define %a @%s(%s) {@\n%a@]@\n}" pp_ret args (Sub.name sub)
    (pp_args args) (pp_body ret) blks

let filter_sub sub =
  (String.starts_with ~prefix:"_" (Sub.name sub)
  || String.starts_with ~prefix:"." (Sub.name sub)
  || String.starts_with ~prefix:"sub" (Sub.name sub)
  || Sub.name sub = "frame_dummy"
  || Sub.name sub = "register_tm_clones"
  || Sub.name sub = "deregister_tm_clones"
  || String.contains (Sub.name sub) '-'
  || String.contains (Sub.name sub) ':')
  |> not

let pp_prog proj ppf prog =
  let target = Project.target proj in
  set_stack target;
  set_sp target;
  set_regs target;
  set_mem target;
  set_ret_reg target;
  Term.enum sub_t prog |> Seq.iter ~f:set_sub;
  let prog =
    Term.map sub_t prog ~f:(fun sub ->
        if filter_sub sub then
          sub |> update_args |> update_rets |> Sub.ssa |> Sub.flatten
          |> update_stack |> transfer_regs |> update_main
        else sub)
  in
  fprintf ppf "@cpu = addrspace(1) global [140 x i8] undef\n";
  fprintf ppf "@stack = addrspace(0) global [65536 x i8] undef\n";
  Term.enum sub_t prog |> Seq.filter ~f:filter_sub
  |> Seq.iter ~f:(fprintf ppf "@[%a@]@\n" pp_sub)

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
