module Z3Seq = Z3.Seq
module Expr = Z3.Expr
open Monads.Std.Monad.Reader

let ctx : (Z3.context, Z3.context) Monads.Std.Monad.Reader.reader = read ()

let create_str str =
  let* ctx = read () in
  return (Z3Seq.mk_string ctx str)

let str_sort = !$Z3Seq.mk_string_sort ctx

let const_str str =
  let* ctx = read () in
  let* str_sort = str_sort in
  return (Expr.mk_const_s ctx str str_sort)

let char_sort = !$Z3Seq.mk_char_sort ctx
let seq_sort ~elem_sort = !$$Z3Seq.mk_seq_sort ctx elem_sort
let unit_seq elem = !$$Z3Seq.mk_seq_unit ctx elem
let concat seq1 seq2 = !$$Z3Seq.mk_seq_concat ctx (all [ seq1; seq2 ])
let prefix seq1 seq2 = !$$$Z3Seq.mk_seq_prefix ctx seq1 seq2
let suffix seq1 seq2 = !$$$Z3Seq.mk_seq_suffix ctx seq1 seq2

let contains_str ~needle ~haystack =
  !$$$Z3Seq.mk_seq_contains ctx haystack needle

let str_len str = !$$Z3Seq.mk_seq_length ctx str
