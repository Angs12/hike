open Bap.Std
open Bap_main
open Bap.Std.Bil.Types
open Bap_core_theory
open Bap_core_theory.Theory.Value
open Regular.Std
open Either
open Format
module MonadReader = Monads.Std.Monad.Reader
module StrMap = Map.Make (String)

type i32

let i32 : i32 Theory.Bitv.t Theory.Value.sort = Theory.Bitv.define 32

type i64

let i64 : i64 Theory.Bitv.t Theory.Value.sort = Theory.Bitv.define 64

type i8

let i8 : i8 Theory.Bitv.t Theory.Value.sort = Theory.Bitv.define 8

type b

let b : Theory.Bool.t Theory.Value.sort = Theory.Bool.t

type mem64

let mem64 : (i64, i8) Theory.Mem.t Theory.Value.sort = Theory.Mem.define i64 i8

type mem32

let mem32 : (i32, i8) Theory.Mem.t Theory.Value.sort = Theory.Mem.define i32 i8

type varsort = BITVEC32 | BITVEC64 | BITVEC8 | ARRAY32 | ARRAY64 | BOOL

let var_sort sort =
  if sort = Sort.forget i32 then BitVectorZ3.bitvector_sort ~size:32
  else if sort = Sort.forget i64 then BitVectorZ3.bitvector_sort ~size:64
  else if sort = Sort.forget i8 then BitVectorZ3.bitvector_sort ~size:8
  else if sort = Sort.forget b then BooleanZ3.bool_sort
  else if sort = Sort.forget mem64 then
    ArrayZ3.bitvec_sort ~index_size:64 ~data_size:8
  else if sort = Sort.forget mem32 then
    ArrayZ3.bitvec_sort ~index_size:32 ~data_size:8
  else failwith "define_var_smt : sort not supported"

let define_var_smt ~identifier var =
  let sort = Var.sort var in
  if sort = Sort.forget i32 then BitVectorZ3.const_bitvector ~size:32 identifier
  else if sort = Sort.forget i64 then
    BitVectorZ3.const_bitvector ~size:64 identifier
  else if sort = Sort.forget i8 then
    BitVectorZ3.const_bitvector ~size:8 identifier
  else if sort = Sort.forget b then BooleanZ3.const_bool identifier
  else if sort = Sort.forget mem64 then
    let index_sort = BitVectorZ3.bitvector_sort ~size:64 in
    let data_sort = BitVectorZ3.bitvector_sort ~size:8 in
    ArrayZ3.const_array ~index_sort ~data_sort identifier
  else if sort = Sort.forget mem32 then
    let index_sort = BitVectorZ3.bitvector_sort ~size:32 in
    let data_sort = BitVectorZ3.bitvector_sort ~size:8 in
    ArrayZ3.const_array ~index_sort ~data_sort identifier
  else failwith "define_var_smt : sort not supported"

let init_sub sub =
  Sub.free_vars sub
  |> Var.Set.fold ~init:StrMap.empty ~f:(fun map var ->
         StrMap.add (Var.name var)
           (define_var_smt ~identifier:(Var.name var) var)
           map)

let trivial_expr expr var_defs =
  match expr with
  | Var v -> StrMap.find (Var.name v) var_defs
  | Int w ->
      let open BitVectorZ3 in
      let size = Word.bitwidth w in
      let v_sort = bitvector_sort ~size in
      GenericZ3.imediate_sort
        (w |> Word.to_int64_exn |> Int64.to_string)
        ~sort:v_sort
  | _ -> failwith "trivial_expr: non-bitvector var"

let rec expr_size expr =
  match expr with
  | Var v -> (
      match Var.typ v with
      | Imm n -> n
      | _ -> failwith "trivial_expr_size: non-bitvector var")
  | Int w -> Word.bitwidth w
  | BinOp (op, e1, _) -> (
      match op with
      | PLUS -> expr_size e1
      | MINUS -> expr_size e1
      | TIMES -> expr_size e1
      | DIVIDE -> expr_size e1
      | SDIVIDE -> expr_size e1
      | MOD -> expr_size e1
      | SMOD -> expr_size e1
      | LSHIFT -> expr_size e1
      | RSHIFT -> expr_size e1
      | ARSHIFT -> expr_size e1
      | AND -> expr_size e1
      | OR -> expr_size e1
      | XOR -> expr_size e1
      | EQ -> 1
      | NEQ -> 1
      | LT -> 1
      | SLT -> 1
      | LE -> 1
      | SLE -> 1)
  | UnOp (_, e) -> expr_size e
  | Cast (cast, i, e) -> (
      match cast with
      | LOW -> i
      | HIGH -> i
      | SIGNED -> expr_size e
      | UNSIGNED -> expr_size e)
  | Unknown _ -> failwith "trivial_expr_size: unknown"
  | Let (_, _, e) -> expr_size e
  | Load (_, _, _, size) -> Size.in_bytes size * 8
  | Store (_, _, _, _, _) -> failwith "trivial_expr_size: store"
  | Extract (_, _, _) -> failwith "trivial_expr_size: extract"
  | Concat (_, _) -> failwith "trivial_expr_size: concat"
  | Ite (_, _, _) -> failwith "trivial_expr_size: ite"

let unop_smt (op, e) =
  let open BitVectorZ3 in
  match op with
  | NEG ->
      fprintf Format.err_formatter "NEG\n";
      neg e
  | NOT ->
      fprintf Format.err_formatter "NOT\n";
      bit_not e

let binop_smt (op, e1, e2) =
  let open BitVectorZ3 in
  match op with
  | PLUS -> e1 ++ e2
  | MINUS -> e1 -- e2
  | TIMES -> e1 @@ e2
  | DIVIDE -> udiv e1 e2
  | SDIVIDE -> sdiv e1 e2
  | MOD -> urem e1 e2
  | SMOD -> srem e1 e2
  | LSHIFT -> shl e1 e2
  | RSHIFT -> lshr e1 e2
  | ARSHIFT -> ashr e1 e2
  | AND -> e1#&&e2
  | OR -> e1#||e2
  | XOR -> e1#^^e2
  | EQ -> e1 == e2
  | NEQ -> e1 ==! e2
  | LT -> ult e1 e2
  | SLT -> slt e1 e2
  | LE -> ule e1 e2
  | SLE -> sle e1 e2

let store_big_endian_byte idx data size arr n =
  let open BitVectorZ3 in
  let bitvec_sort = GenericZ3.get_sort idx in
  let n_bitvec =
    GenericZ3.imediate_sort
      (Base.Int.to_string (size - n - 1))
      ~sort:bitvec_sort
  in
  let byte = extract ~high:(((n + 1) * 8) - 1) ~low:(n * 8) data in
  ArrayZ3.store ~array:arr ~index:(idx ++ n_bitvec) ~value:byte

let store_little_endian_byte idx data arr n =
  let open BitVectorZ3 in
  let bitvec_sort = GenericZ3.get_sort idx in
  let n_bitvec =
    GenericZ3.imediate_sort (Base.Int.to_string n) ~sort:bitvec_sort
  in
  let byte = extract ~high:(((n + 1) * 8) - 1) ~low:(n * 8) data in
  ArrayZ3.store ~array:arr ~index:(idx ++ n_bitvec) ~value:byte

let store_smtarray arr idx data endian size =
  match endian with
  | LittleEndian ->
      List.fold_left
        (store_little_endian_byte idx data)
        arr
        (List.init size (fun x -> x))
  | BigEndian ->
      List.fold_left
        (store_big_endian_byte idx data size)
        arr
        (List.init size (fun x -> x))

let load_big_endian_byte idx arr n =
  let open BitVectorZ3 in
  let bitvec_sort = GenericZ3.get_sort idx in
  let n_bitvec =
    GenericZ3.imediate_sort (Base.Int.to_string n) ~sort:bitvec_sort
  in
  ArrayZ3.select ~array:arr ~index:(idx ++ n_bitvec)

let load_little_endian_byte idx size arr n =
  let open BitVectorZ3 in
  let bitvec_sort = GenericZ3.get_sort idx in
  let n_bitvec =
    GenericZ3.imediate_sort
      (Base.Int.to_string (size - n - 1))
      ~sort:bitvec_sort
  in
  ArrayZ3.select ~array:arr ~index:(idx ++ n_bitvec)

let list_seq l ~f =
  let init = List.hd l in
  List.fold_left (fun acc x -> f acc x) init (List.tl l)

let load_smtarray arr idx endian size =
  match endian with
  | LittleEndian ->
      List.map
        (load_little_endian_byte idx size arr)
        (List.init size (fun x -> x))
      |> list_seq ~f:BitVectorZ3.concat
  | BigEndian ->
      List.map (load_big_endian_byte idx arr) (List.init size (fun x -> x))
      |> list_seq ~f:BitVectorZ3.concat

let var_exn var = match var with Var v -> v | _ -> failwith "var_expr"
let left_exn = function Left x -> x | Right _ -> failwith "left_exn"

let rec expr2smt_formula var_defs expr =
  match expr with
  | Var v -> Left (StrMap.find (Var.name v) !var_defs)
  | UnOp (op, e) ->
      let e = left_exn (expr2smt_formula var_defs e) in
      Left (unop_smt (op, e))
  | BinOp (op, e1, e2) ->
      let e1 = left_exn (expr2smt_formula var_defs e1) in
      let e2 = left_exn (expr2smt_formula var_defs e2) in
      Left (binop_smt (op, e1, e2))
  | Int w ->
      let open BitVectorZ3 in
      let size = Word.bitwidth w in
      let v_sort = bitvector_sort ~size in
      Left
        (GenericZ3.imediate_sort
           (w |> Word.to_int64_exn |> Int64.to_string)
           ~sort:v_sort)
  | Load (mem, addr, endian, size) ->
      let mem = var_exn mem in
      let size = Size.in_bytes size in
      let addr = left_exn (expr2smt_formula var_defs addr) in
      let mem = StrMap.find (Var.name mem) !var_defs in
      Left (load_smtarray mem addr endian size)
  | Store (mem, addr, data, endian, size) ->
      let mem = var_exn mem in
      let size = Size.in_bytes size in
      fprintf Format.err_formatter "Storing %d bytes at %s\n" size
        (Var.str () mem);
      let addr = left_exn (expr2smt_formula var_defs addr) in
      let data = left_exn (expr2smt_formula var_defs data) in
      let mem = StrMap.find (Var.name mem) !var_defs in
      Left (store_smtarray mem addr data endian size)
  | Cast (cast, i, e) -> (
      let expr = left_exn (expr2smt_formula var_defs e) in
      let size = expr_size e in
      fprintf Format.err_formatter "Extracting bits for casting: %d -> %d \n"
        size i;
      match cast with
      | LOW -> Left (BitVectorZ3.extract ~high:(i - 1) ~low:0 expr)
      | HIGH -> Left (BitVectorZ3.extract ~high:(size - 1) ~low:(size - i) expr)
      | SIGNED ->
          Left
            (BitVectorZ3.extract ~high:(size - 1) ~low:0 expr
            |> BitVectorZ3.sext ~size:i)
      | UNSIGNED ->
          Left
            (BitVectorZ3.extract ~high:(size - 1) ~low:0 expr
            |> BitVectorZ3.zext ~size:i))
  | Unknown _ -> Right None
  | Let (var, exp1, exp2) ->
      expr2smt_formula var_defs (Exp.substitute (Var var) exp1 exp2)
  | Ite (cond, e1, e2) ->
      let cond = left_exn (expr2smt_formula var_defs cond) in
      let e1 = left_exn (expr2smt_formula var_defs e1) in
      let e2 = left_exn (expr2smt_formula var_defs e2) in
      Left (BooleanZ3.ite ~if_pred:cond ~then_expr:e1 ~else_expr:e2)
  | Concat (e1, e2) ->
      let e1 = left_exn (expr2smt_formula var_defs e1) in
      let e2 = left_exn (expr2smt_formula var_defs e2) in
      Left (BitVectorZ3.concat e1 e2)
  | Extract (high, low, e) ->
      let e = left_exn (expr2smt_formula var_defs e) in
      Left (BitVectorZ3.extract ~high ~low e)

let blk2smt_formula var_defs blk =
  let open MonadReader in
  let open BooleanZ3 in
  Term.enum phi_t blk
  |> Bap.Std.Seq.iter ~f:(fun phi ->
         let var = Phi.lhs phi in
         var_defs :=
           StrMap.add (Var.name var)
             (define_var_smt ~identifier:(Var.name var) var)
             !var_defs);
  Term.enum def_t blk
  |> Seq.fold ~init:[] ~f:(fun asserts def ->
         let var = Def.lhs def in
         let expr = Def.rhs def in
         fprintf Format.err_formatter "Defining var: %s\n" (Var.name var);
         let rhs = expr2smt_formula var_defs expr in
         match rhs with
         | Right None ->
             let lhs = define_var_smt ~identifier:(Var.name var) var in
             var_defs := StrMap.add (Var.name var) lhs !var_defs;
             return asserts
         | Right (Some rhs_sort) ->
             let lhs = GenericZ3.const (Var.name var) ~sort:rhs_sort in
             var_defs := StrMap.add (Var.name var) lhs !var_defs;
             return asserts
         | Left rhs ->
             let rhs_sort = rhs >>| Z3.Expr.get_sort in
             let lhs = GenericZ3.const (Var.name var) ~sort:rhs_sort in
             var_defs := StrMap.add (Var.name var) lhs !var_defs;
             let* lhs_sort = lhs >>| Z3.Expr.get_sort in
             fprintf Format.err_formatter "lhs_sort: %s\n"
               (Z3.Sort.to_string lhs_sort);
             let* e1 = !$Z3.Expr.to_string lhs in
             let* e2 = !$Z3.Expr.to_string rhs in
             let* temp_sort = rhs_sort in
             let s = Z3.Sort.to_string temp_sort in
             fprintf Format.err_formatter "Creating assert: %s = %s : %s\n" e1
               e2 s;
             return @@ ((lhs == rhs) :: asserts))

let predicate_simplify asserts =
  let open MonadReader in
  let params = SolverZ3.create_params in
  let _ = SolverZ3.set_param_bool params "sort_store" true in
  let _ = SolverZ3.set_param_bool params "flat" true in
  let _ = SolverZ3.set_param_bool params "flat_and_or" true in
  let _ = SolverZ3.set_param_bool params "bit2bool" true in
  let _ = SolverZ3.set_param_bool params "bv_extract_prop" true in
  let _ = SolverZ3.set_param_bool params "expand_store_eq" true in
  Base.List.map asserts ~f:(fun a -> SolverZ3.simplify params a) |> return

let get_asserts var_defs term =
  let open MonadReader in
  printf "Generating asserts from block: %s\n" (Term.name term);
  print_flush ();
  fprintf Format.err_formatter "Generating asserts from block\n";
  let* asserts = blk2smt_formula var_defs term >>= predicate_simplify in
  let* sets = all asserts in
  fprintf Format.err_formatter "Printing asserts\n";
  Base.List.iter sets ~f:(fun set ->
      fprintf Format.err_formatter "%s\n" (Z3.Expr.to_string set));
  return sets

let rec dfs sub var_defs asserts visited ctx tid =
  let graph = Sub.to_graph sub in
  Graphs.Tid.Node.succs tid graph
  |> Seq.fold ~init:asserts ~f:(fun asserts tid ->
         if Tid.Set.mem !visited tid then asserts
         else if Graphs.Tid.exit = tid then asserts
         else
           let term = Term.find blk_t sub tid in
           let open MonadReader in
           match term with
           | Some term ->
               let asserts =
                 Blk.Map.add_exn ~key:term
                   ~data:(run (get_asserts var_defs term) ctx)
                   asserts
               in
               visited := Tid.Set.add !visited tid;
               dfs sub var_defs asserts visited ctx tid
           | None -> failwith "print_formulas: term not found")

let print_formulas sub var_defs ctx =
  let start = Graphs.Tid.start in
  let visited = ref Tid.Set.empty in
  let asserts = Blk.Map.empty in
  dfs sub var_defs asserts visited ctx start

let phi2smt_formula var_defs phi =
  let lhs = Phi.lhs phi in
  let vals = Phi.values phi in
  let lhs_exp = trivial_expr (Var lhs) !var_defs in
  let open BooleanZ3 in
  Seq.map vals ~f:(fun (_, e) ->
      let rhs = expr2smt_formula var_defs e in
      match rhs with Right _ -> bool_true | Left rhs -> lhs_exp == rhs)
  |> Seq.fold ~init:bool_false ~f:(fun e1 e2 -> e1 ^^ e2)

let jmp2smt_formula var_defs jmp =
  let cond = Jmp.cond jmp in
  let var = expr2smt_formula var_defs cond |> left_exn in
  BitVectorZ3.bit_not var |> BitVectorZ3.bv1_to_bool

let is_phi elt = match elt with `Phi _ -> true | _ -> false
let is_def elt = match elt with `Def _ -> true | _ -> false
let is_jmp elt = match elt with `Jmp _ -> true | _ -> false

let get_phi_term elt =
  match elt with `Phi phi -> phi | _ -> failwith "get_phi_term: not a phi"

let get_def_term elt =
  match elt with `Def def -> def | _ -> failwith "get_def_term: not a def"

let get_jmp_term elt =
  match elt with `Jmp jmp -> jmp | _ -> failwith "get_jmp_term: not a jmp"

let phi_asserts var_defs blk =
  Blk.elts blk
  |> Bap.Std.Seq.filter ~f:is_phi
  |> Bap.Std.Seq.map ~f:(fun phi ->
         let phi = get_phi_term phi in
         phi2smt_formula var_defs phi)
  |> Bap.Std.Seq.to_list_rev

let add_phi_asserts var_defs blk asserts =
  let phi_asserts = phi_asserts var_defs blk in
  Base.List.concat [ phi_asserts; asserts ]

let rec reachable_blks graph visited node =
  let label = Graphs.Ir.Node.label node in
  if Blk.Set.mem visited label then visited
  else
    let preds = Graphs.Ir.Node.preds node graph in
    let visited = Blk.Set.add visited label in
    Seq.fold preds ~init:visited ~f:(reachable_blks graph)

let entry_point graph =
  Seq.find_exn (Graphs.Ir.nodes graph) ~f:(fun node ->
      Graphs.Ir.Node.degree ~dir:`In node graph = 0)
  |> Graphs.Ir.Node.label |> Term.tid

let reachability var_defs graph node jmp_edge asserts mem =
  let open MonadReader in
  let reachable_blks = reachable_blks graph Blk.Set.empty node in
  let asserts =
    Blk.Map.filter_keys ~f:(fun key -> Blk.Set.mem reachable_blks key) asserts
    |> Blk.Map.mapi ~f:(fun ~key ~data -> add_phi_asserts var_defs key data)
    |> Blk.Map.data |> Base.List.concat
  in
  let blk = Graphs.Ir.Node.label node in
  let jmps = Graphs.Ir.Edge.jmps `before jmp_edge graph in
  let jmp_exprs =
    Bap.Std.Seq.map jmps ~f:(jmp2smt_formula var_defs)
    |> Bap.Std.Seq.to_list_rev
  in
  let cond = Jmp.cond (Graphs.Ir.Edge.jmp jmp_edge) in
  fprintf Format.err_formatter "Jmp guard: %s\n" (Exp.to_string cond);
  let phi_asserts = phi_asserts var_defs blk in
  let expr =
    [ expr2smt_formula var_defs cond |> left_exn |> BitVectorZ3.bv1_to_bool ]
  in
  let* p_jmps = all jmp_exprs in
  fprintf Format.err_formatter "Jmp expr: \n";
  Base.List.iter p_jmps ~f:(fun set ->
      fprintf Format.err_formatter "%s\n" (Z3.Expr.to_string set));
  fprintf Format.err_formatter "Jmp cond: \n";
  let* p_exprs = all expr in
  Base.List.iter p_exprs ~f:(fun set ->
      fprintf Format.err_formatter "%s\n" (Z3.Expr.to_string set));
  fprintf Format.err_formatter "Mem: \n";
  let* p_mem = all mem in
  Base.List.iter p_mem ~f:(fun set ->
      fprintf Format.err_formatter "%s\n" (Z3.Expr.to_string set));
  return @@ Base.List.concat [ mem; expr; jmp_exprs; phi_asserts; asserts ]

let lift_to_monad exp_list = List.map MonadReader.return exp_list

let calculate_sat var_defs graph node jmp asserts mem =
  let open MonadReader in
  let asserts = reachability var_defs graph node jmp asserts mem in
  let* asserts = asserts in
  let* predicates = all asserts in
  fprintf Format.err_formatter
    "==============Predicate asserts==================\n";
  Base.List.iter predicates ~f:(fun set ->
      fprintf Format.err_formatter "%s\n" (Z3.Expr.to_string set));
  fprintf Format.std_formatter "Testing jump: %s\n"
    (Graphs.Ir.Edge.to_string jmp);
  print_flush ();
  let sat = SolverZ3.is_sat asserts in
  let* unwrapped_sat = sat in
  if unwrapped_sat then print_endline "SAT" else print_endline "UNSAT";
  sat

let print_sat var_defs graph node jmp asserts mem =
  let open MonadReader in
  let asserts = reachability var_defs graph node jmp asserts mem in
  let* asserts = asserts in
  let* predicates = all asserts in
  fprintf Format.err_formatter
    "==============Predicate asserts==================\n";
  Base.List.iter predicates ~f:(fun set ->
      fprintf Format.err_formatter "%s\n" (Z3.Expr.to_string set));
  fprintf Format.std_formatter "Testing jump: %s\n"
    (Graphs.Ir.Edge.to_string jmp);
  print_flush ();
  SolverZ3.solve asserts

let init_memory var_defs proj =
  let memory = Project.memory proj in
  let memmap = Memmap.to_sequence memory in
  let bits = Project.target proj |> Theory.Target.bits in
  let byte_size = Project.target proj |> Theory.Target.byte in
  let bvbytesort = BitVectorZ3.bitvector_sort ~size:byte_size in
  let bvbitssort = BitVectorZ3.bitvector_sort ~size:bits in
  let index_sort = BitVectorZ3.bitvector_sort ~size:bits in
  let data_sort = BitVectorZ3.bitvector_sort ~size:byte_size in
  let mem = ArrayZ3.const_array ~index_sort ~data_sort "mem" in
  var_defs := StrMap.add "mem" mem !var_defs;
  let global_mem, _ =
    Seq.find_exn memmap ~f:(fun (_, x) ->
        Value.get Image.section x = Some ".data")
  in
  let empty_mem = ArrayZ3.const_array ~index_sort ~data_sort "empty_mem" in
  let initialized_mem =
    Memory.foldi global_mem ~init:empty_mem ~f:(fun addr var array ->
        let v = Word.to_int_exn var |> Int.to_string in
        let value = GenericZ3.imediate_sort ~sort:bvbytesort v in
        let i = Word.to_int_exn addr |> Int.to_string in
        let index = GenericZ3.imediate_sort ~sort:bvbitssort i in
        let open BooleanZ3 in
        ArrayZ3.store ~array ~index ~value)
  in
  let open BooleanZ3 in
  [ mem == initialized_mem ]

let merge_nodes graph node1 node2 =
  let blk1 = Graphs.Ir.Node.label node1 in
  let blk2 = Graphs.Ir.Node.label node2 in
  let phis =
    Blk.elts blk1
    |> Bap.Std.Seq.filter ~f:is_phi
    |> Bap.Std.Seq.to_list_rev |> List.map get_phi_term
  in
  let defs1 =
    Blk.elts blk1
    |> Bap.Std.Seq.filter ~f:is_def
    |> Bap.Std.Seq.to_list |> List.map get_def_term
  in
  let defs2 =
    Blk.elts blk2
    |> Bap.Std.Seq.filter ~f:is_def
    |> Bap.Std.Seq.to_list |> List.map get_def_term
  in
  let jmps =
    Blk.elts blk2
    |> Bap.Std.Seq.filter ~f:is_jmp
    |> Bap.Std.Seq.to_list |> List.map get_jmp_term
  in
  let defs = List.concat [ defs1; defs2 ] in
  let tid = Term.tid blk1 in
  let blk = Blk.create ~defs ~phis ~jmps ~tid () in
  Graphs.Ir.Node.update node1 blk graph |> Graphs.Ir.Node.remove node2

let merge_cfg sub =
  let rec merge graph =
    let nodes = Graphs.Ir.nodes graph in
    let node1 =
      Seq.find nodes ~f:(fun node ->
          Graphs.Ir.Node.degree ~dir:`Out node graph = 1
          && Graphs.Ir.Node.degree ~dir:`In
               (Graphs.Ir.Edge.dst
                  (Graphs.Ir.Node.outputs node graph |> Seq.hd_exn))
               graph
             = 1)
    in
    match node1 with
    | None -> graph
    | Some node1 ->
        let node2 =
          Graphs.Ir.Edge.dst (Graphs.Ir.Node.outputs node1 graph |> Seq.hd_exn)
        in
        merge_nodes graph node1 node2 |> merge
  in
  let graph = Sub.to_cfg sub in
  let new_graph = merge graph in
  Graphs.Ir.pp Format.std_formatter new_graph;
  Sub.of_cfg new_graph

let some_exn = function Some x -> x | None -> failwith "some_exn"

let limit_stack_pointer var_defs proj mem =
  let open BooleanZ3 in
  let target = Project.target proj in
  let sp =
    Theory.Target.reg target Theory.Role.Register.stack_pointer |> some_exn
  in
  let fp =
    Theory.Target.reg target Theory.Role.Register.frame_pointer |> some_exn
  in
  let sp_sort = var_sort (Theory.Var.sort sp) in
  let fp_sort = var_sort (Theory.Var.sort fp) in
  let limit_sp =
    BitVectorZ3.ugt_bool
      (StrMap.find (Theory.Var.name sp) !var_defs)
      (GenericZ3.imediate_sort "50000" ~sort:sp_sort)
  in
  let limit_fp =
    BitVectorZ3.ugt_bool
      (StrMap.find (Theory.Var.name fp) !var_defs)
      (GenericZ3.imediate_sort "50000" ~sort:fp_sort)
  in
  limit_sp :: limit_fp :: mem

let remove_opaque proj sub =
  Sub.pp Format.err_formatter sub;
  let cfg = [ ("model", "true"); ("proof", "true") ] in
  let var_defs = ref (init_sub sub) in
  let mem = init_memory var_defs proj in
  let mem = limit_stack_pointer var_defs proj mem in
  let ctx = Z3.mk_context cfg in
  let _ = Z3.Log.open_ "./logz3" in
  fprintf Format.err_formatter "Z3 was initialized\n";
  fprintf Format.err_formatter "%s\n" (Z3.Expr.get_simplify_help ctx);
  let asserts = print_formulas sub var_defs ctx in
  let asserts = Blk.Map.map asserts ~f:lift_to_monad in
  let graph = Sub.to_cfg sub in
  Graphs.Ir.pp Format.std_formatter graph;
  let entry = entry_point graph in
  let nodes = Graphs.Ir.nodes graph in
  let res =
    Seq.map nodes ~f:(fun node ->
        let jmps = Graphs.Ir.Node.outputs node graph in
        Seq.map jmps ~f:(fun jmp ->
            ( MonadReader.run
                (calculate_sat var_defs graph node jmp asserts mem)
                ctx,
              jmp )))
  in
  let new_graph =
    Seq.concat res
    |> Seq.fold ~init:graph ~f:(fun graph (sat, jmp) ->
           if not sat then Graphs.Ir.Edge.remove jmp graph else graph)
  in
  let rec remove_unreachable_nodes graph =
    let nodes = Graphs.Ir.nodes graph in
    let unreachable_nodes =
      Seq.filter nodes ~f:(fun node ->
          Graphs.Ir.Node.degree ~dir:`In node graph = 0
          && Graphs.Ir.Node.label node |> Term.tid != entry)
    in
    if Seq.is_empty unreachable_nodes then graph
    else
      let graph =
        Seq.fold unreachable_nodes ~init:graph ~f:(fun graph node ->
            Graphs.Ir.Node.remove node graph)
      in
      remove_unreachable_nodes graph
  in
  let new_graph = remove_unreachable_nodes new_graph in
  Graphs.Ir.pp Format.std_formatter new_graph;
  Sub.of_cfg new_graph

let get_pass (name : string) =
  Bil.passes () |> Base.List.find ~f:(fun p -> Bil.Pass.name p = name)

let print_solve proj sub =
  let open BooleanZ3 in
  Sub.pp Format.err_formatter sub;
  let var_defs = ref (init_sub sub) in
  let cfg = [ ("model", "true"); ("proof", "true") ] in
  let mem = init_memory var_defs proj in
  let mem = limit_stack_pointer var_defs proj mem in
  let ctx = Z3.mk_context cfg in
  let _ = Z3.Log.open_ "./logz3" in
  fprintf Format.err_formatter "Z3 was initialized\n";
  fprintf Format.err_formatter "%s\n" (Z3.Expr.get_simplify_help ctx);
  let asserts = print_formulas sub var_defs ctx in
  let asserts = Blk.Map.map asserts ~f:lift_to_monad in
  let graph = Sub.to_cfg sub in
  let node = Graphs.Ir.nodes graph |> Seq.hd_exn in
  let edge = Graphs.Ir.Node.outputs node graph |> Seq.to_list_rev |> List.hd in
  MonadReader.run (print_sat var_defs graph node edge asserts mem) ctx

let main proj =
  let normalization = Base.Option.value_exn @@ get_pass "bnf1" in
  let optimizations =
    Base.List.map
      ~f:(fun pass -> Base.Option.value_exn @@ get_pass pass)
      [ "constant-propagation"; "prune-dead-virtuals"; "constant-folding" ]
  in
  Bil.select_passes @@ (normalization :: optimizations);
  let prog = Project.program proj in
  let arch = Project.arch proj in
  let sub =
    Term.enum sub_t prog |> Seq.to_list_rev
    |> List.find (fun sub -> Sub.name sub = "factorial")
    |> Sub.ssa |> Deadcode.clean_sub arch
  in
  print_solve proj sub

let () =
  Extension.declare @@ fun _ctxt ->
  Project.register_pass' main;
  Ok ()
