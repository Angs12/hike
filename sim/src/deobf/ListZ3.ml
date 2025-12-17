module Z3List = Z3.Z3List
open Monads.Std.Monad.Reader
open FunctionZ3

let list_sort identifier ~data_sort =
  let* ctx = read () in
  let* data_sort = data_sort in
  return (Z3List.mk_list_s ctx identifier data_sort)

let int_list = list_sort "Int List" ~data_sort:NumberZ3.int_sort

let insert ~data ~l =
  let l_sort = !$Z3.Expr.get_sort l in
  let cons = !$Z3List.get_cons_decl l_sort in
  apply ~f:cons ~args:[ data; l ]

let nil_func ~list_sort = !$Z3List.get_nil_decl list_sort

let head l =
  let l_sort = !$Z3.Expr.get_sort l in
  let head = !$Z3List.get_head_decl l_sort in
  apply ~f:head ~args:[ l ]

let tail l =
  let l_sort = !$Z3.Expr.get_sort l in
  let tail = !$Z3List.get_cons_decl l_sort in
  apply ~f:tail ~args:[ l ]

let is_nil l =
  let l_sort = !$Z3.Expr.get_sort l in
  let is_nil = !$Z3List.get_is_nil_decl l_sort in
  apply ~f:is_nil ~args:[ l ]

let is_cons l =
  let l_sort = !$Z3.Expr.get_sort l in
  let is_cons = !$Z3List.get_is_cons_decl l_sort in
  apply ~f:is_cons ~args:[ l ]
