module Boolean = Z3.Boolean
open Monads.Std.Monad.Reader

let ctx : (Z3.context, Z3.context) Monads.Std.Monad.Reader.reader = read ()

(** xor *)
let ( ^^ ) expr1 expr2 = !$$$Boolean.mk_xor ctx expr1 expr2

(** or *)
let ( || ) expr1 expr2 = !$$Boolean.mk_or ctx (all [ expr1; expr2 ])

(** implies *)
let ( => ) expr1 expr2 = !$$$Boolean.mk_implies ctx expr1 expr2

(** and *)
let ( && ) expr1 expr2 = !$$Boolean.mk_and ctx (all [ expr1; expr2 ])

(** equal *)
let ( == ) expr1 expr2 = !$$$Boolean.mk_eq ctx expr1 expr2

(** not *)
let ( ~! ) expr = !$$Boolean.mk_not ctx expr

(** not equal *)
let ( ==! ) expr1 expr2 =
  !$$Boolean.mk_not ctx (!$$$Boolean.mk_eq ctx expr1 expr2)

(** if i then t else e *)
let ite ~if_pred ~then_expr ~else_expr =
  !$$$$Boolean.mk_ite ctx if_pred then_expr else_expr

let bool_true = !$Boolean.mk_true ctx
let bool_false = !$Boolean.mk_false ctx
let bool_sort = !$Boolean.mk_sort ctx
let is_bool expr = Boolean.is_bool expr

let const_bool identifier =
  let* ctx = read () in
  return (Boolean.mk_const_s ctx identifier)
