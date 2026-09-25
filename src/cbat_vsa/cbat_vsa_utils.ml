(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

(* Cbat_vsa_utils: small shared utilities. Every def is denoted. *)

exception NotImplemented of string

(* Raised by [not_implemented] without a [~top] fallback. *)

(* Placeholder degrading to [~top]. *)
let not_implemented ?(top : 'a option) component : 'a = match top with
  | None -> raise (NotImplemented component)
  | Some tp ->
    (* Log through Event.Log. *)
    Bap.Std.Event.Log.message Bap.Std.Event.Log.Warning
      ~section:"cbat_vsa"
      "not_implemented: %s (degrading to top)" component;
    tp

(* Max elements of an exact set. *)
let fin_set_size : int = 10

(* Max progressions in a canonical piece union. *)
let max_pieces : int = 4

(* Integer division rounding up. *)
let cdiv_int (x : int) (y : int) : int = (x - 1)/y + 1

open !Core
open Bap.Std

let exn_on_err : ('a, Type.error) Result.t -> 'a = function
  | Ok e -> e
  | Error e -> raise (Type.Error.T e)

let rotate_list (l : 'a list) : 'a list =
  let l_r = List.rev l in
  match l_r with
  | [] -> []
  | hd::tl -> hd::(List.rev tl)

(* Negation of a comparison op: symmetric ops complement in place;
   ordering ops complement AND swap ([!(a < b)] = [b <= a]).  Total —
   the result is always one of the understood comparisons. *)
let negate_comparison (op : Bil.binop) : Bil.binop * bool =
  match op with
  | Bil.LT -> (Bil.LE, true)
  | Bil.LE -> (Bil.LT, true)
  | Bil.SLT -> (Bil.SLE, true)
  | Bil.SLE -> (Bil.SLT, true)
  | Bil.EQ -> (Bil.NEQ, false)
  | Bil.NEQ -> (Bil.EQ, false)
  | Bil.PLUS | Bil.MINUS | Bil.TIMES | Bil.DIVIDE | Bil.SDIVIDE
  | Bil.MOD | Bil.SMOD | Bil.LSHIFT | Bil.RSHIFT | Bil.ARSHIFT
  | Bil.AND | Bil.OR | Bil.XOR -> assert false

let is_comparison_op (op : Bil.binop) : bool =
  match op with
  | Bil.EQ | Bil.NEQ | Bil.LT | Bil.LE | Bil.SLT | Bil.SLE -> true
  | _ -> false

(* The complete form of a cond: every negation sits in a comparison, so
   the evaluator constrains the cond TRUE and needs no polarity rule.
   NOT over a comparison is the negated comparison; NOT over a NOT
   folds; AND sides complete; NOT over any other shape stays (the
   walk's NOT row is the bijection). *)
let rec complete_cond (e : exp) : exp =
  match e with
  | Bil.BinOp (Bil.AND, a, b) ->
    Bil.BinOp (Bil.AND, complete_cond a, complete_cond b)
  | Bil.UnOp (Bil.NOT, u) -> negated_cond u
  | _ -> e

and negated_cond (e : exp) : exp =
  match e with
  | Bil.BinOp (op, a, b) when is_comparison_op op ->
    let op', swap = negate_comparison op in
    if swap then Bil.BinOp (op', b, a) else Bil.BinOp (op', a, b)
  | Bil.UnOp (Bil.NOT, u) -> complete_cond u
  | _ -> Bil.UnOp (Bil.NOT, e)
