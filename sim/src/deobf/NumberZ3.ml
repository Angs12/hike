module Arithmetic = Z3.Arithmetic
open Monads.Std.Monad.Reader

let ctx : (Z3.context, Z3.context) Monads.Std.Monad.Reader.reader = read ()

(** add *)
let ( ++ ) expr1 expr2 = !$$Arithmetic.mk_add ctx (all [ expr1; expr2 ])

(** mod *)
let ( %% ) expr1 expr2 = !$$$Arithmetic.Integer.mk_mod ctx expr1 expr2

(** div *)
let ( // ) expr1 expr2 = !$$$Arithmetic.mk_div ctx expr1 expr2

(** mul *)
let ( @@ ) expr1 expr2 = !$$Arithmetic.mk_mul ctx (all [ expr1; expr2 ])

(** greater than *)
let ( >> ) expr1 expr2 = !$$$Arithmetic.mk_gt ctx expr1 expr2

(** greater or equal than *)
let ( >= ) expr1 expr2 = !$$$Arithmetic.mk_ge ctx expr1 expr2

(** less than *)
let ( << ) expr1 expr2 = !$$$Arithmetic.mk_lt ctx expr1 expr2

(** less or equal than *)
let ( =< ) expr1 expr2 = !$$$Arithmetic.mk_le ctx expr1 expr2

(** sub *)
let ( -- ) expr1 expr2 = !$$Arithmetic.mk_sub ctx (all [ expr1; expr2 ])

let int_sort = !$Arithmetic.Integer.mk_sort ctx
let real_sort = !$Arithmetic.Real.mk_sort ctx

let const_int identifier =
  let* ctx = read () in
  return (Arithmetic.Integer.mk_const_s ctx identifier)

let const_real identifier =
  let* ctx = read () in
  return (Arithmetic.Real.mk_const_s ctx identifier)

let imediate num =
  let* ctx = read () in
  return (Arithmetic.Integer.mk_numeral_i ctx num)
