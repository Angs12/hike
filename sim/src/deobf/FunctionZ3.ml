module FuncInterp = Z3.Model.FuncInterp
module FuncDecl = Z3.FuncDecl
module Quantifier = Z3.Quantifier
open Monads.Std.Monad.Reader

let ctx : (Z3.context, Z3.context) Monads.Std.Monad.Reader.reader = read ()
let apply ~f ~args = !$$FuncDecl.apply f (all args)

let lambda ~args ~expr =
  let lambda_q = !$$$Quantifier.mk_lambda_const ctx (all args) expr in
  !$Quantifier.expr_of_quantifier lambda_q

let func_decl name ~args_sort ~ret_sort =
  let* ctx = read () in
  let* ret_val = ret_sort in
  let* args = all args_sort in
  return (FuncDecl.mk_func_decl_s ctx name args ret_val)

let apply_lamda ~lamda ~args =
  let args = all args in
  !$$Z3.Expr.substitute_vars lamda args
