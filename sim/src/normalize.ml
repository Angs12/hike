open Bap.Std
open Bap.Std.Bil.Types
include Self ()

let endian_str endian =
  match endian with LittleEndian -> "LE" | BigEndian -> "BE"

let normalize_var v =
  match Bap.Std.Var.is_physical v with true -> "REG" | false -> "VAR"

let cast_str cast =
  match cast with
  | SIGNED -> "SIGNED"
  | UNSIGNED -> "UNSIGNED"
  | HIGH -> "HIGH"
  | LOW -> "LOW"

let normalize_jmp kind =
  match kind with
  | Call call -> (
      match Call.target call with
      | Direct _ -> "Direct call"
      | Indirect _ -> "Indirect call")
  | Ret label -> (
      match label with
      | Direct _ -> "Direct return"
      | Indirect _ -> "Indirect return")
  | Int (int, _) -> Format.sprintf "Interrupt %d\n" int
  | Goto label -> (
      match label with
      | Direct _ -> "Direct goto"
      | Indirect _ -> "Indirect goto")

let rec normalize_expr expr =
  match expr with
  | BinOp (op, e1, e2) ->
      (match op with
      | PLUS -> "ADD"
      | MINUS -> "SUB"
      | TIMES -> "MUL"
      | DIVIDE -> "DIV"
      | SDIVIDE -> "SDIV"
      | MOD -> "MOD"
      | SMOD -> "SMOD"
      | AND -> "AND"
      | OR -> "OR"
      | XOR -> "XOR"
      | LSHIFT -> "LSL"
      | RSHIFT -> "LSR"
      | ARSHIFT -> "ASR"
      | EQ -> "EQ"
      | NEQ -> "NE"
      | LT -> "LT"
      | SLT -> "SLT"
      | LE -> "LE"
      | SLE -> "SLE")
      ^ "(" ^ normalize_expr e1 ^ ", " ^ normalize_expr e2 ^ ")"
  | UnOp (op, e) -> (
      match op with
      | NEG -> "NEG(" ^ normalize_expr e ^ ")"
      | NOT -> "NOT(" ^ normalize_expr e ^ ")")
  | Var v -> (
      match Bap.Std.Var.is_physical v with true -> "REG" | false -> "VAR")
  | Int _ -> "INT"
  | Unknown (name, _) -> name
  | Extract (hi, lo, e) ->
      "EXTRACT(" ^ string_of_int hi ^ ", " ^ string_of_int lo ^ ", "
      ^ normalize_expr e ^ ")"
  | Load (mem, addr, endian, _) ->
      "LOAD(" ^ normalize_expr mem ^ ", " ^ normalize_expr addr ^ ", "
      ^ endian_str endian ^ ")"
  | Store (mem, addr, e, endian, _) ->
      "STORE(" ^ normalize_expr mem ^ ", " ^ normalize_expr addr ^ ", "
      ^ endian_str endian ^ ", " ^ normalize_expr e ^ ")"
  | Let (_, _, _) -> "LET"
  | Ite (c, t, e) ->
      "ITE(" ^ normalize_expr c ^ ", " ^ normalize_expr t ^ ", "
      ^ normalize_expr e ^ ")"
  | Cast (c, i, e) ->
      cast_str c ^ " " ^ string_of_int i ^ "(" ^ normalize_expr e ^ ")"
  | Concat (e1, e2) ->
      "CONCAT(" ^ normalize_expr e1 ^ ", " ^ normalize_expr e2 ^ ")"

let normalize_phi p =
  let vals = Phi.values p in
  Seq.map vals ~f:(fun (_, e) -> normalize_expr e)
  |> Seq.to_list |> String.concat " / "

let normalizer =
  object
    inherit [string list] Term.visitor

    method! enter_def d stmts =
      (normalize_var (Def.lhs d) ^ " = " ^ normalize_expr (Def.rhs d)) :: stmts

    method! enter_phi p stmts =
      (normalize_var (Phi.lhs p) ^ " = " ^ normalize_phi p) :: stmts

    method! enter_jmp j stmts =
      ("IF "
      ^ normalize_expr (Jmp.cond j)
      ^ " THEN "
      ^ normalize_jmp (Jmp.kind j))
      :: stmts
  end
