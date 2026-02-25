module Z3Array = Z3.Z3Array
open Monads.Std.Monad.Reader

let ctx : (Z3.context, Z3.context) Monads.Std.Monad.Reader.reader = read ()
let store ~array ~index ~value = !$$$$Z3Array.mk_store ctx array index value
let select ~array ~index = !$$$Z3Array.mk_select ctx array index

let const_array identifier ~index_sort ~data_sort =
  let* ctx = read () in
  let* index = index_sort in
  let* data = data_sort in
  return (Z3Array.mk_const_s ctx identifier index data)

let bitvec_sort ~index_size ~data_size =
  let index = BitVectorZ3.bitvector_sort ~size:index_size in
  let data = BitVectorZ3.bitvector_sort ~size:data_size in
  !$$$Z3Array.mk_sort ctx index data

let array_ext ~array1 ~array2 = !$$$Z3Array.mk_array_ext ctx array1 array2
