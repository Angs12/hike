open Decl_parser
open Bap.Std
open Bap.Std.Bil.Types

type typeclass = MEMORY of int
type retclass = RET | HIDDEN

let rec type_size (t : functype) : int =
  match t with
  | Void -> 0
  | Pointer -> 64
  | Int n -> n
  | Half -> 16
  | Bfloat -> 32
  | Float -> 32
  | Double -> 64
  | FP128 -> 128
  | X86fp80 -> 80
  | PPCfp128 -> 128
  | X86amx -> 128
  | Struct ts ->
      Base.List.fold_left ts ~init:0 ~f:(fun acc t -> acc + type_size t)

let arg_type_classification (ts : functype list) : typeclass list =
  Base.List.filter_map ts ~f:(fun t ->
      match t with Void -> None | _ -> Some (MEMORY (type_size t)))

let ret_classification (t : functype) : retclass =
  if type_size t <= 32 then RET else HIDDEN

let args (ts : functype list) (ret : functype) =
  let args = arg_type_classification ts in
  let args = if ret_classification ret = RET then args else MEMORY 32 :: args in
  let sp = Var.create "ESP" (Imm 64) in
  let mem = Var.create "stack" (Mem (`r64, Size.r8)) in
  (* skip return adress from stack *)
  let sp = Bil.BinOp (PLUS, Var sp, Int (Word.of_int ~width:32 4)) in
  Base.List.mapi args ~f:(fun i (MEMORY n) ->
      let sp = Bil.BinOp (PLUS, sp, Int (Word.of_int ~width:32 (i * 4))) in
      let arg_size = (n / 32 * 32) + if n mod 32 = 0 then 0 else 32 in
      (Load (Var mem, sp, BigEndian, Size.of_int_exn arg_size), Imm arg_size))

let return (t : functype) : var list =
  let eax = Var.create "EAX" (Imm 64) in
  match t with Void -> [] | _ -> [ eax ]
