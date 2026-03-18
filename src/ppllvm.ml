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
module Libcmap = Map.Make (String)
module KB = Bap_knowledge.Knowledge

let llvm_ptr_tag =
  Value.Tag.register ~name:"llvm-ptr"
    ~uuid:"6d1cdeb3-22c8-11f1-b8fa-f4a80dc1b6bb"
    (module Core.Unit)

let return_arg_tag =
  Value.Tag.register ~name:"return-arg"
    ~uuid:"60b819ea-22cb-11f1-ba62-f4a80dc1b6bb"
    (module Core.Unit)

module LlvmType = struct
  let package = "convlir"

  type tag = Category
  type sort = unit
  type types = Ptr | Int | Float | Void

  let name = "llvm-types"
  let desc = "A class representing types in LLVM IR"
  let index = ()
  let type_cls : (tag, sort) KB.cls = KB.Class.declare name index ~package ~desc

  let type_domain : types KB.Domain.t =
    KB.Domain.flat "llvm-types-domain" ~empty:Float
      ~equal:(fun t1 t2 ->
        match (t1, t2) with
        | Int, Int -> true
        | Ptr, Ptr -> true
        | Float, Float -> true
        | Void, Void -> true
        | _, _ -> false)
      ~inspect:(fun t ->
        match t with
        | Int -> Sexplib.Sexp.Atom "int"
        | Ptr -> Sexplib.Sexp.Atom "ptr"
        | Float -> Sexplib.Sexp.Atom "float"
        | Void -> Sexplib.Sexp.Atom "void")

  let typ : (tag, types) KB.slot =
    KB.Class.property type_cls "type" type_domain ~package
end

let () =
  Toplevel.exec
    begin
      let open KB.Syntax in
      let* typ = KB.Object.create LlvmType.type_cls in
      let* () = KB.provide LlvmType.typ typ LlvmType.Ptr in
      let* typ = KB.collect LlvmType.typ typ in
      (match typ with
      | Ptr -> fprintf err_formatter "Ptr@."
      | Int -> fprintf err_formatter "Int@."
      | Float -> fprintf err_formatter "Float@."
      | Void -> fprintf err_formatter "Void@.");

      KB.return ()
    end

type trivial_exp = Var of Var.t | Int of Word.t
type function_decl = string * Decl_parser.functype

let subs = ref StrMap.empty

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
          fprintf err_formatter "Section: %s@.%a@." name Memory.pp mem))

let is_mem var = match Var.typ var with Mem _ -> true | _ -> false

let var_size var =
  match Var.typ var with Imm n -> n | _ -> failwith "pp exp type: non-imm var"

let free_vars sub =
  Sub.free_vars sub
  |> Var.Set.filter ~f:(fun var -> not @@ is_mem var)
  |> Var.Set.to_list

let set_sub sub =
  if Term.tid sub |> Tid.name = "@main" then
    subs :=
      StrMap.add "@main"
        (Seq.singleton (Arg.create ~intent:Out !ret_reg (Var !ret_reg)))
        !subs
  else
    let free_vars = free_vars sub in
    let ret = Arg.create ~intent:Out !ret_reg (Var !ret_reg) in
    let ret = Term.set_attr ret return_arg_tag () in
    subs :=
      StrMap.add
        (Term.tid sub |> Tid.name)
        (Seq.of_list
           (ret
           :: Base.List.map
                ~f:(fun reg ->
                  let arg_var =
                    Var.create (Sub.name sub ^ Var.name reg) (Var.typ reg)
                  in
                  Arg.create ~intent:In arg_var (Var reg))
                free_vars))
        !subs

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

let set_libc target libc =
  let abi =
    if Theory.Target.matches target "x86_64-gnu-elf" then
      (module Gnu64_abi : Abi)
    else failwith "abi not supported"
  in
  let module Abi = (val abi : Abi) in
  Libcmap.iter
    (fun name (data : Decl_parser.funcdef) ->
      let ret = Abi.return data.return in
      let args = Abi.args data.args data.return in
      let func_decl =
        Seq.of_list
          (List.map (fun r -> Arg.create ~intent:Out r (Var r)) ret
          @ List.mapi
              (fun i (a, intent) ->
                let arg_var =
                  Var.create (name ^ sprintf "arg%d" i) (arg_type a)
                in
                Arg.create ~intent arg_var a)
              args)
      in
      subs := StrMap.add ("@" ^ name) func_decl !subs)
    libc

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
let stack_len = 2048

let correct_registers tid regs =
  object
    inherit Exp.mapper

    method! map_var var =
      if Var.same var !ret_reg then
        Var (create_reg ~name:("ret_" ^ Var.name var) ~tid ~typ:(Var.typ var))
      else if Base.List.mem regs var ~equal:Var.same then
        Var (create_reg ~name:("reg_" ^ Var.name var) ~tid ~typ:(Var.typ var))
      else Var var
  end

let pp_mem_type mem =
  match mem with
  | Var v -> (
      match Var.typ v with
      | Mem _ ->
          if Var.name v = "stack" then "ptr addrspace(0)"
          else "ptr addrspace(1)"
      | _ -> failwith "pp mem type: non-mem var")
  | _ -> failwith "pp mem type: non-var expression"

let ptr_type exp =
  match exp with
  | Var v -> (
      match Var.typ v with
      | Mem (`r32, _) -> Imm 32
      | Mem (`r64, _) -> Imm 64
      | _ -> failwith "pp ptr type: non-mem var")
  | _ -> failwith "pp ptr type: non-var expression"

let size_type size = Imm (Size.in_bits size)

let pp_trivial_exp_exn exp =
  let sub =
    String.map (fun c ->
        if c = '#' then '_'
        else if c = '.' then '_'
        else if c = '%' then '_'
        else c)
  in
  match exp with
  | Bil.Var v -> (
      match Var.typ v with
      | Imm _ | Unk -> sprintf "%%var_%s" (sub (Var.name v))
      | Mem _ ->
          if Var.name v = "stack" then "@stack"
          else sprintf "%%%s" (sub (Var.name v)))
  | Int i -> Int64.to_string (Word.to_int64_exn i)
  | _ -> failwith "pp trivial exp : non-trivial exp"

let pp_trivial_exp exp =
  let sub =
    String.map (fun c ->
        if c = '#' then '_'
        else if c = '.' then '_'
        else if c = '%' then '_'
        else if c = '\\' then '_'
        else c)
  in
  match exp with
  | Var v -> (
      match Var.typ v with
      | Imm _ | Unk -> sprintf "%%var_%s" (sub (Var.name v))
      | Mem _ ->
          if Var.name v = "stack" then "@stack"
          else sprintf "%%%s" (sub (Var.name v)))
  | Int i -> Int64.to_string (Word.to_int64_exn i)

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

let word_type word = Imm (Word.bitwidth word)
let exp_type exp = match exp with Int i -> word_type i | Var v -> Var.typ v

let var_type var =
  match Var.typ var with
  | Imm n -> sprintf "i%d" n
  | _ -> failwith "var_type : non-imm var"

let exps_type (exp1 : trivial_exp) (exp2 : trivial_exp) =
  let t1 = exp_type exp1 in
  let t2 = exp_type exp2 in
  Type.max t1 t2

let type_str t =
  match t with Imm n -> sprintf "i%d" n | _ -> failwith "type_str"

let pp_types exp1 exp2 =
  let t1 = exp_type exp1 in
  let t2 = exp_type exp2 in
  type_str @@ Type.max t1 t2

let pp_type exp = type_str @@ exp_type exp

let pp_binop (op, e1, e2) =
  sprintf "%s %s %s, %s" (binop_str op) (pp_types e1 e2) (pp_trivial_exp e1)
    (pp_trivial_exp e2)

let all_ones (exp : trivial_exp) =
  match exp with
  | Int i -> Word.ones @@ Word.bitwidth i
  | Var v -> (
      match Var.typ v with
      | Imm n -> Word.ones n
      | _ -> failwith "pp all ones: non-imm var")

let pp_unop ((op, e) : unop * trivial_exp) =
  match op with
  | NEG -> sprintf "sub %s 0, %s" (pp_type e) (pp_trivial_exp e)
  | NOT ->
      sprintf "xor %s %s, %s" (pp_type e)
        (Int64.to_string (Word.to_int64_exn (all_ones e)))
        (pp_trivial_exp e)

let exp_type_size (exp : trivial_exp) =
  match exp with
  | Int i -> Word.bitwidth i
  | Var v -> (
      match Var.typ v with
      | Imm n -> n
      | _ -> failwith "pp exp type: non-imm var")

let pp_concat ppf ((var, exp1, exp2) : var * trivial_exp * trivial_exp) =
  let temp_var1 = pp_trivial_exp (Var var) ^ "_tmp1" in
  let temp_var2 = pp_trivial_exp (Var var) ^ "_tmp2" in
  let temp_var3 = pp_trivial_exp (Var var) ^ "_tmp3" in
  fprintf ppf "\t%s = zext %s %s to %s\n" temp_var1 (pp_type exp1)
    (pp_trivial_exp exp1) (var_type var);
  fprintf ppf "\t%s = shl %s %s, %d\n" temp_var2 (var_type var) temp_var1
    (exp_type_size exp2);
  fprintf ppf "\t%s = zext %s %s to %s\n" temp_var3 (pp_type exp2)
    (pp_trivial_exp exp2) (var_type var);
  fprintf ppf "\t%s = and %s %s, %s\n" (pp_trivial_exp (Var var)) (var_type var)
    temp_var2 temp_var3

let pp_extract ppf (var, hi, lo, exp) =
  let temp_var = pp_trivial_exp (Var var) ^ "_tmp" in
  fprintf ppf "\t%s = lshr %s %s, %d\n" temp_var (pp_type exp)
    (pp_trivial_exp exp) lo;
  let result_size = hi - lo + 1 in
  fprintf ppf "\t%s = trunc %s %s to i%d\n" (pp_trivial_exp (Var var))
    (pp_type exp) temp_var result_size

let pp_load ppf (var, _, addr, size) =
  let temp_var = pp_trivial_exp (Var var) ^ "_ptr" in
  fprintf ppf "\t%s = inttoptr %s %s to ptr\n" temp_var (pp_type addr)
    (pp_trivial_exp addr);
  fprintf ppf "\t%s = load i%d, ptr %s\n" (pp_trivial_exp (Var var))
    (Size.in_bits size) temp_var

let pp_store ppf (mem, addr, data) =
  let temp_var = Var.create ~is_virtual:true ~fresh:true "" (ptr_type mem) in
  fprintf ppf "\t%s = inttoptr %s %s to ptr\n"
    (pp_trivial_exp (Var temp_var))
    (pp_type addr) (pp_trivial_exp addr);
  fprintf ppf "\tstore %s %s, ptr %s\n" (pp_type data) (pp_trivial_exp data)
    (pp_trivial_exp (Var temp_var))

let pp_cast ppf (var, cast, i, exp) =
  let var_name = pp_trivial_exp (Var var) in
  match cast with
  | UNSIGNED ->
      fprintf ppf "\t%s = zext %s %s to i%d\n" var_name (pp_type exp)
        (pp_trivial_exp exp) i
  | SIGNED ->
      fprintf ppf "\t%s = sext %s %s to i%d\n" var_name (pp_type exp)
        (pp_trivial_exp exp) i
  | HIGH ->
      fprintf ppf "\t%s_tmp = lshr %s %s, %d\n" var_name (pp_type exp)
        (pp_trivial_exp exp)
        (exp_type_size exp - i);
      fprintf ppf "\t%s = trunc %s %s_tmp to i%d\n" var_name (pp_type exp)
        var_name i
  | LOW ->
      fprintf ppf "\t%s = trunc %s %s to i%d\n" var_name (pp_type exp)
        (pp_trivial_exp exp) i

let rec pp_exp ?res ppf exp : trivial_exp =
  match exp with
  | BinOp (op, e1, e2) ->
      let var1 = pp_exp ppf e1 in
      let var2 = pp_exp ppf e2 in
      let res =
        Option.value res
          ~default:
            (Var.create ~is_virtual:true ~fresh:true "" (exps_type var1 var2))
      in
      fprintf ppf "\t%s = %s\n" (pp_trivial_exp (Var res))
        (pp_binop (op, var1, var2));
      Var res
  | UnOp (op, e) ->
      let var = pp_exp ppf e in
      let res =
        Option.value res
          ~default:(Var.create ~is_virtual:true ~fresh:true "" (exp_type var))
      in
      fprintf ppf "\t%s = %s\n" (pp_trivial_exp (Var res)) (pp_unop (op, var));
      Var res
  | Var v -> Var v
  | Int i -> Int i
  | Cast (cast, i, exp) ->
      let exp = pp_exp ppf exp in
      let res =
        Option.value res
          ~default:(Var.create ~is_virtual:true ~fresh:true "" (Imm i))
      in
      pp_cast ppf (res, cast, i, exp);
      Var res
  | Load (mem, addr, _, size) ->
      let mem = pp_exp ppf mem in
      let addr = pp_exp ppf addr in
      let res =
        Option.value res
          ~default:(Var.create ~is_virtual:true ~fresh:true "" (size_type size))
      in
      pp_load ppf (res, mem, addr, size);
      Var res
  | Concat (exp1, exp2) ->
      let exp1 = pp_exp ppf exp1 in
      let exp2 = pp_exp ppf exp2 in
      let res =
        Option.value res
          ~default:
            (Var.create ~is_virtual:true ~fresh:true ""
               (Imm (exp_type_size exp1 + exp_type_size exp2)))
      in
      pp_concat ppf (res, exp1, exp2);
      Var res
  | Extract (hi, lo, exp) ->
      let exp = pp_exp ppf exp in
      let res =
        Option.value res
          ~default:
            (Var.create ~is_virtual:true ~fresh:true "" (Imm (hi - lo + 1)))
      in
      pp_extract ppf (res, hi, lo, exp);
      Var res
  | Store (mem, addr, data, _, _) ->
      let mem = pp_exp ppf mem in
      let addr = pp_exp ppf addr in
      let data = pp_exp ppf data in
      pp_store ppf (mem, addr, data);
      mem
  | Unknown _ -> failwith "pp_exp: Unknown expression"
  | _ -> failwith "pp_exp: Ite and Let expressions"

let pp_exp ppf res (exp : exp) =
  match exp with
  | Var v -> (
      match Var.typ v with
      | Imm _ | Unk ->
          fprintf ppf "\t%s = add %s %s, 0\n" (pp_trivial_exp (Var res))
            (pp_type (Var res)) (pp_trivial_exp (Var v))
      | Mem _ ->
          fprintf ppf "\t%s = ptrtoint ptr %s to %s\n"
            (pp_trivial_exp (Var res)) (pp_trivial_exp (Var v))
            (var_type !ret_reg))
  | Int i ->
      fprintf ppf "\t%s = add %s %s, 0\n" (pp_trivial_exp (Var res))
        (pp_type (Var res))
        (Word.to_int64_exn i |> Int64.to_string)
  | _ -> pp_exp ~res ppf exp |> ignore

let label_tid label =
  match label with
  | Direct tid -> tid
  | Indirect _ -> failwith "label_tid: indirect label"

let pp_cond ppf cond tid =
  let cond_var = create_virtual ~name:"cond" ~tid ~typ:(Imm 1) in
  pp_exp ppf cond_var cond

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
    pp_exp ppf cond_var cond;
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
      pp_exp ppf res
        (Exp.substitute (Var !ret_reg) (Var new_ret) (Arg.rhs return_reg))

let is_void tid =
  let args =
    Base.Option.value_exn
      ~message:(sprintf "is_void: sub %s not found" (Tid.name tid))
      (StrMap.find_opt (Tid.name tid) !subs)
  in
  Seq.for_all args ~f:(fun arg ->
      match Arg.intent arg with
      | Some i -> ( match i with In -> true | Out -> false | Both -> true)
      | None -> true)

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

let pp_def ppf def =
  let var = Def.lhs def in
  match Def.rhs def with Unknown _ -> () | _ -> pp_exp ppf var (Def.rhs def)

let ready_call_args ppf sub_tid tid =
  let args =
    Base.Option.value_exn
      ~message:(sprintf "ready_call_args: sub %s not found" (Tid.name sub_tid))
      (StrMap.find_opt (Tid.name sub_tid) !subs)
  in
  Seq.iter args ~f:(fun arg ->
      match Arg.intent arg with
      | Some i -> (
          match i with
          | Out -> ()
          | In ->
              let var = Arg.lhs arg in
              let var =
                create_reg ~name:(Var.name var) ~tid ~typ:(Var.typ var)
              in
              let exp = Exp.map (correct_registers tid !regs) (Arg.rhs arg) in
              pp_exp ppf var exp
          | Both ->
              let var = Arg.lhs arg in
              let tmp_var =
                create_reg ~name:(Var.name var ^ "_tmp") ~tid ~typ:(Var.typ var)
              in
              let var =
                create_reg ~name:(Var.name var) ~tid ~typ:(Var.typ var)
              in
              let exp = Exp.map (correct_registers tid !regs) (Arg.rhs arg) in
              pp_exp ppf tmp_var exp;
              fprintf ppf "\t%s = call zeroext %s @_address_map_(%s %s)\n"
                (pp_trivial_exp (Var var)) (var_type var) (var_type tmp_var)
                (pp_trivial_exp (Var tmp_var)))
      | None -> ())

let pp_args sub_tid tid =
  let args =
    Base.Option.value_exn
      ~message:(sprintf "pp_args: sub %s not found" (Tid.name sub_tid))
      (StrMap.find_opt (Tid.name sub_tid) !subs)
  in
  let args =
    Seq.fold args ~init:"" ~f:(fun prev arg ->
        let var = Arg.lhs arg in
        let var = create_reg ~name:(Var.name var) ~tid ~typ:(Var.typ var) in
        match Arg.intent arg with
        | Some i -> (
            match i with
            | In | Both ->
                sprintf "%s %s %s," prev (var_type var)
                  (pp_trivial_exp (Var var))
            | Out -> prev)
        | None -> prev)
  in
  if args = "" then "" else String.sub args 0 (String.length args - 1)

let pp_func_call blk_tid ret_var fallthrough target ppf =
  ready_call_args ppf target blk_tid;
  if not @@ is_void target then
    fprintf ppf "\t%s = call zeroext %s %s(%s)\n"
      (pp_trivial_exp (Var ret_var))
      (var_type ret_var) (pp_func target) (pp_args target blk_tid)
  else
    fprintf ppf "\tcall %s %s(%s)\n" "void" (pp_func target)
      (pp_args target blk_tid);
  fprintf ppf "\tbr label %%%s\n" (pp_label fallthrough)

let pp_call blk_tid ret ppf call =
  match (Call.return call, Call.target call) with
  | None, _ ->
      fprintf ppf "\tret %s %s\n" (pp_type (Var ret)) (pp_trivial_exp (Var ret))
  | Some (Direct ret_label), Direct target_label ->
      pp_func_call blk_tid ret ret_label target_label ppf
  | _, _ -> failwith "pp_call: non-trivial return type"

let pp_phi ppf phi =
  let var = Phi.lhs phi in
  if is_mem var || Base.List.mem !regs var ~equal:Var.same then ()
  else
    let var_name = pp_trivial_exp (Var var) in
    let vals = Phi.values phi in
    let values =
      Seq.fold vals ~init:"" ~f:(fun prev (tid, exp) ->
          sprintf "%s [%s,%%%s]," prev (pp_trivial_exp_exn exp) (pp_label tid))
    in
    let values = String.sub values 0 (String.length values - 1) in
    fprintf ppf "\t%s = phi %s %s\n" var_name (var_type var) values

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

let pp_elts blk ppf elts =
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
      pp_call tid res ppf call

let update_args sub =
  let builder =
    Sub.Builder.create ~tid:(Term.tid sub) ~name:(Sub.name sub) ()
  in
  Seq.iter (Term.enum blk_t sub) ~f:(fun blk -> Sub.Builder.add_blk builder blk);
  Sub.Builder.result builder

let pp_body ppf =
  Seq.iter ~f:(fun blk ->
      fprintf ppf "\n%s:\n%a\n"
        (pp_label (Term.tid blk))
        (pp_elts blk) (Blk.elts blk))

let entry_blk_tid sub =
  let blks = Term.enum blk_t sub in
  Term.tid (Seq.hd_exn blks)

let update_stack sub =
  Term.map blk_t sub ~f:(fun blk ->
      let builder =
        Blk.Builder.init ~same_tid:true ~copy_phis:true ~copy_jmps:true blk
      in
      Seq.iter (Term.enum def_t blk) ~f:(fun def ->
          if is_mem (Def.lhs def) then ()
          else
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
          let builder = Blk.Builder.init ~copy_phis:false ~copy_jmps:true blk in
          Base.List.iter !regs ~f:(fun reg ->
              let reg_var =
                create_reg ~name:(Var.name reg) ~tid:(Term.tid blk)
                  ~typ:(Var.typ reg)
              in
              if reg = !sp then (
                let data =
                  Bil.Int
                    (Word.of_int ~width:(var_size reg_var) (stack_len - 1))
                in
                let ptr =
                  create_reg
                    ~name:(Var.name reg ^ "_ptr")
                    ~tid:(Term.tid blk) ~typ:(Var.typ reg)
                in
                let def = Def.create ptr (Var !stack) in
                Blk.Builder.add_def builder def;
                let exp = Bil.binop Bil.PLUS (Bil.Var ptr) data in
                let def = Def.create reg_var exp in
                Blk.Builder.add_def builder def)
              else
                let data = Bil.Int (Word.of_int ~width:(var_size reg_var) 0) in
                let def = Def.create reg_var data in
                Blk.Builder.add_def builder def);
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
            let reg =
              create_reg ~name:(Var.name base) ~tid ~typ:(Var.typ base)
            in
            Var.Map.add_exn map ~key:base ~data:reg)
      in
      let blk =
        Base.List.fold ~init:blk !regs ~f:(fun blk base ->
            let ver = ref 0 in
            let reg =
              create_reg ~name:(Var.name base) ~tid ~typ:(Var.typ base)
            in
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
      if not (Seq.to_list blk_incoming = [ Graphs.Tid.start ]) then
        Var.Map.iteri !reg_map ~f:(fun ~key ~data:_ ->
            let var = create_reg ~name:(Var.name key) ~tid ~typ:(Var.typ key) in
            let phi_rhs =
              Seq.fold blk_incoming ~init:[] ~f:(fun prev tid ->
                  if tid = Graphs.Tid.start then
                    let reg_var =
                      Var.create (Sub.name sub ^ Var.name key) (Var.typ key)
                    in
                    (Term.tid blk, Bil.Var reg_var) :: prev
                  else
                    let reg_var =
                      create_reg
                        ~name:("reg_" ^ Var.name key)
                        ~tid ~typ:(Var.typ key)
                    in
                    (tid, Bil.Var reg_var) :: prev)
            in
            let phi = Phi.of_list var phi_rhs in
            Blk.Builder.add_phi builder phi)
      else if not (Sub.name sub = "main") then
        let free_vars = free_vars sub in
        Base.List.iter !regs ~f:(fun var ->
            let reg = create_reg ~name:(Var.name var) ~tid ~typ:(Var.typ var) in
            let def =
              if not @@ Base.List.mem free_vars var ~equal:Var.same then
                let data = Bil.Int (Word.of_int ~width:(var_size var) 0) in
                Def.create reg data
              else
                let arg_var =
                  create_reg
                    ~name:(Sub.name sub ^ Var.name var)
                    ~tid:(Term.tid sub) ~typ:(Var.typ var)
                in
                Def.create reg (Var arg_var)
            in
            Blk.Builder.add_def builder def)
      else ();
      Blk.elts blk
      |> Seq.iter ~f:(fun elt ->
          match elt with `Def def -> Blk.Builder.add_def builder def | _ -> ());
      Var.Map.iteri !reg_map ~f:(fun ~key ~data ->
          match (cf_type (Term.enum jmp_t blk), Var.same key !ret_reg) with
          | Call, true ->
              let reg_var =
                create_reg ~name:("ret_" ^ Var.name key) ~tid ~typ:(Var.typ key)
              in
              let def = Def.create reg_var (Var data) in
              Blk.Builder.add_def builder def
          | _, _ ->
              let reg_var =
                create_reg ~name:("reg_" ^ Var.name key) ~tid ~typ:(Var.typ key)
              in
              let def = Def.create reg_var (Var data) in
              Blk.Builder.add_def builder def);
      Blk.Builder.result builder)

let pp_ret ppf () = fprintf ppf "%s" (pp_type (Var !ret_reg))

let pp_sub ppf sub =
  let blks = Term.enum blk_t sub in
  let tid = Term.tid sub in
  fprintf ppf "@[<2>define %a %s(%s) {@\n%a@]@\n}" pp_ret ()
    (pp_func @@ Term.tid sub)
    (pp_args tid tid) pp_body blks

let is_libc libc sub =
  Libcmap.mem (Sub.name sub) libc
  || Base.String.is_substring ~substring:":external" (Sub.name sub)

let arr2llvm arr =
  let data =
    Base.Array.fold ~init:"" ~f:(fun acc v -> acc ^ sprintf "i8 %d," v) arr
  in
  (* remove last comma *)
  let data =
    if data = "" then "" else String.sub data 0 (String.length data - 1)
  in
  data

let pp_global ~is_const ppf mem name =
  let str = arr2llvm mem in
  match is_const with
  | true ->
      fprintf ppf "@%s = addrspace(0) constant [%d x i8] [ %s ]\n" name
        (Array.length mem) str
  | false ->
      fprintf ppf "@%s = addrspace(0) global [%d x i8] [ %s ]\n" name
        (Array.length mem) str

let get_bil_pass name =
  Base.List.find_exn ~f:(fun pass -> Bil.Pass.name pass = name) (Bil.passes ())

let get_pass name =
  Project.find_pass name
  |> Base.Option.value_exn ~message:("pass " ^ name ^ " not found")

let run_pass proj name =
  let pass = get_pass name in
  Project.Pass.run_exn pass proj

let pp_prog ppf prog =
  Seq.iter ~f:(fprintf ppf "@[%a@]@\n" pp_sub) (Term.enum sub_t prog)

let setup proj libc =
  let target = Project.target proj in
  set_ret_reg target;
  set_regs target;
  set_stack target;
  set_sp target;
  set_mem target;
  set_libc target libc

let pp_address_map ppf target data_mem rodata_mem =
  fprintf ppf
    "\n\
    \    define i%d @_address_map_(i%d %%ptr) {\n\
    \        %%is_rodata1 = icmp uge i%d %%ptr, u%a\n\
    \        %%is_rodata2 = icmp ule i%d %%ptr, u%a\n\
    \        %%is_rodata = and i1 %%is_rodata1, %%is_rodata2\n\n\
    \        %%is_data1 = icmp uge i%d %%ptr, u%a\n\
    \        %%is_data2 = icmp ule i%d %%ptr, u%a\n\
    \        %%is_data = and i1 %%is_data1, %%is_data2\n\n\
    \        br i1 %%is_rodata, label %%isrodata , label %%fallthrough1\n\n\
    \        \n\
    \        fallthrough1:\n\
    \        br i1 %%is_data, label %%isdata, label %%fallthrough2\n\n\
    \        fallthrough2:\n\
    \        ret i64 %%ptr\n\n\
    \        isrodata:\n\
    \        %%rodata_ptr = ptrtoint ptr @rodata to i%d\n\
    \        %%rodata_offset = sub i%d %%ptr, u%a\n\
    \        %%rodata_addr = add i%d %%rodata_ptr, %%rodata_offset\n\
    \        ret i64 %%rodata_addr\n\n\
    \        isdata:\n\
    \        %%data_ptr = ptrtoint ptr @data to i%d\n\
    \        %%data_offset = sub i%d %%ptr, u%a\n\
    \        %%data_addr = add i%d %%data_ptr, %%data_offset\n\
    \        ret i64 %%data_addr\n\
    \    }\n\n\
    \    "
    (Theory.Target.bits target)
    (Theory.Target.bits target)
    (Theory.Target.bits target)
    Word.pp
    (Memory.min_addr rodata_mem)
    (Theory.Target.bits target)
    Word.pp
    (Memory.max_addr rodata_mem)
    (Theory.Target.bits target)
    Word.pp (Memory.min_addr data_mem)
    (Theory.Target.bits target)
    Word.pp (Memory.max_addr data_mem)
    (Theory.Target.bits target)
    (Theory.Target.bits target)
    Word.pp
    (Memory.min_addr rodata_mem)
    (Theory.Target.bits target)
    (Theory.Target.bits target)
    (Theory.Target.bits target)
    Word.pp (Memory.min_addr data_mem)
    (Theory.Target.bits target)

let pp ppf proj =
  let proj = run_pass proj "trivial-condition-form" in
  (* print_sections proj; *)
  Project.passes ()
  |> Base.List.iter ~f:(fun pass ->
      fprintf err_formatter "Project pass :: %s \n" (Project.Pass.name pass));
  let rodata = get_section ".rodata" proj in
  let data = get_section ".data" proj in
  let stack = Base.Array.init stack_len ~f:(fun _ -> 0) in
  let prog = Project.program proj in
  let main =
    Base.Option.value_exn ~message:"Main function not found"
      (Term.enum sub_t prog |> Seq.find ~f:(fun sub -> Sub.name sub = "main"))
  in
  let reachable_funcs = Reachable_funcs.reachable_funcs prog main in
  let libc = Decl_parser.parse_header_file "stdio_headers.ll" in
  setup proj libc;
  let proj =
    Project.map_program proj ~f:(fun prog ->
        Term.filter_map sub_t prog ~f:(fun sub ->
            if is_libc libc sub || not (SubSet.mem sub reachable_funcs) then
              None
            else (
              set_sub sub;
              (* Sub.pp err_formatter sub; *)
              Some
                (sub |> update_args |> update_rets |> Sub.ssa |> Sub.flatten
               |> update_stack |> transfer_regs |> update_main))))
  in
  (* let prog = Project.program proj in *)
  (* Program.pp err_formatter prog; *)
  pp_global ~is_const:true ppf rodata "rodata";
  pp_global ~is_const:false ppf data "data";
  pp_global ~is_const:false ppf stack "stack";
  pp_address_map ppf (Project.target proj)
    (get_section_mem ".data" proj)
    (get_section_mem ".rodata" proj);
  fprintf ppf "@[%a@]" pp_prog (Project.program proj)

let main input_program output _ =
  Bil.passes ()
  |> Base.List.iter ~f:(fun pass ->
      fprintf err_formatter "Bil pass :: %s \n" (Bil.Pass.name pass));
  let passes =
    Base.List.map ~f:get_bil_pass
      [ "prune-dead-virtuals"; "constant-folding"; "constant-propagation" ]
  in
  Bil.select_passes passes;
  let ppf = Out_channel.open_text output |> Format.formatter_of_out_channel in
  let loader = "llvm" in
  let proj =
    Project.create @@ Project.Input.load input_program ~loader
    |> Core.Or_error.ok_exn
  in
  pp ppf proj;
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
