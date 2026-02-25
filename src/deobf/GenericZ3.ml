module Expr = Z3.Expr
module Symbol = Z3.Symbol
module Sort = Z3.Sort
module Quantifier = Z3.Quantifier
module Model = Z3.Model
module Datatype = Z3.Datatype
module Constructor = Z3.Datatype.Constructor
open Monads.Std.Monad.Reader

let ctx : (Z3.context, Z3.context) Monads.Std.Monad.Reader.reader = read ()

let declare_sort name =
  let* ctx = read () in
  return (Sort.mk_uninterpreted_s ctx name)

let get_sort expr = !$Expr.get_sort expr

let forall ~bound_vars ~expr =
  let* ctx = read () in
  let* bound_vars = all bound_vars in
  let* expr = expr in
  let forall_q =
    Quantifier.mk_forall_const ctx bound_vars expr (Some 1) [] [] None None
  in
  return (Quantifier.expr_of_quantifier forall_q)

let const identifier ~sort =
  let identifier = return identifier in
  !$$$Expr.mk_const_s ctx identifier sort

let imediate_sort num ~sort =
  let* ctx = read () in
  let* sort = sort in
  return (Expr.mk_numeral_string ctx num sort)

let create_sym name =
  let* ctx = read () in
  return (Symbol.mk_string ctx name)

let apply_option sort =
  match sort with
  | None -> return None
  | Some m ->
      let* a = m in
      return (Some a)

let create_constructor ~adt_name ~cons_name ~body ~sorts ~options =
  let* ctx = read () in
  let* cons_sym = create_sym cons_name in
  let* adt_sym = create_sym adt_name in
  let string_to_sym = Symbol.mk_string ctx in
  let body_sym = Base.List.map ~f:string_to_sym body in
  let* sorts = all (Base.List.map ~f:apply_option sorts) in
  return (Datatype.mk_constructor ctx adt_sym cons_sym body_sym sorts options)

let datatype_sort ~name ~constructors =
  let* ctx = read () in
  let* constructors = all constructors in
  return (Datatype.mk_sort_s ctx name constructors)

let get_constructors ~cons =
  let* cons = cons in
  return (Datatype.get_constructors cons)

let some_or_die n = match n with Some x -> x | None -> exit 1

let nth_cons ~cons ~n =
  let* cons = cons in
  return (some_or_die (Base.List.nth cons n))
