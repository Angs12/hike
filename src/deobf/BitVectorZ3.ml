module BitVector = Z3.BitVector
open Monads.Std.Monad.Reader

let ctx : (Z3.context, Z3.context) Monads.Std.Monad.Reader.reader = read ()

let bitvector_sort ~size =
  let* ctx = read () in
  return (BitVector.mk_sort ctx size)

let const_bitvector identifier ~size =
  let* ctx = read () in
  return (BitVector.mk_const_s ctx identifier size)

let bool_to_bv1 expr =
  let open BooleanZ3 in
  let bv1_sort = bitvector_sort ~size:1 in
  let one = GenericZ3.imediate_sort "1" ~sort:bv1_sort in
  let zero = GenericZ3.imediate_sort "0" ~sort:bv1_sort in
  ite ~if_pred:expr ~then_expr:one ~else_expr:zero

let bv1_to_bool expr =
  let open BooleanZ3 in
  let bv1_sort = bitvector_sort ~size:1 in
  let one = GenericZ3.imediate_sort "1" ~sort:bv1_sort in
  expr == one

let bitvec_size bv =
  let sort = GenericZ3.get_sort bv in
  !$Z3.BitVector.get_size sort

(** bit vector and *)
let ( ++ ) bv1 bv2 = !$$$BitVector.mk_add ctx bv1 bv2

(** bit vector sub *)
let ( -- ) bv1 bv2 = !$$$BitVector.mk_sub ctx bv1 bv2

(** bit vector mul *)
let ( @@ ) bv1 bv2 = !$$$BitVector.mk_mul ctx bv1 bv2

(** bitwise and *)
let ( #&& ) bv1 bv2 = !$$$BitVector.mk_and ctx bv1 bv2

(** bitwise or *)
let ( #|| ) bv1 bv2 = !$$$BitVector.mk_or ctx bv1 bv2

(** bitvector equality *)
let ( == ) bv1 bv2 = BooleanZ3.( == ) bv1 bv2 |> bool_to_bv1

(** bitvector inequality *)
let ( ==! ) bv1 bv2 = BooleanZ3.( ==! ) bv1 bv2 |> bool_to_bv1

(** bitwise not *)
let bit_not bv1 = !$$BitVector.mk_not ctx bv1

(** negation *)
let neg bv1 = !$$BitVector.mk_neg ctx bv1

(** signed remainder*)
let srem bv1 bv2 = !$$$BitVector.mk_srem ctx bv1 bv2

(** unsigned remainder*)
let urem bv1 bv2 = !$$$BitVector.mk_urem ctx bv1 bv2

(** signed division *)
let sdiv bv1 bv2 = !$$$BitVector.mk_sdiv ctx bv1 bv2

(** unsigned division *)
let udiv bv1 bv2 = !$$$BitVector.mk_udiv ctx bv1 bv2

(** bitwise xor *)
let ( #^^ ) bv1 bv2 = !$$$BitVector.mk_xor ctx bv1 bv2

(** arithmetic shift right *)
let ashr bv amt = !$$$BitVector.mk_ashr ctx bv amt

(** logical shift right*)
let lshr bv amt = !$$$BitVector.mk_lshr ctx bv amt

(** shift left*)
let shl bv amt = !$$$BitVector.mk_shl ctx bv amt

(** signed greater than *)
let sgt bv1 bv2 = !$$$BitVector.mk_sgt ctx bv1 bv2 |> bool_to_bv1

let sgt_bool bv1 bv2 = !$$$BitVector.mk_sgt ctx bv1 bv2

(** signed less than *)
let slt bv1 bv2 = !$$$BitVector.mk_slt ctx bv1 bv2 |> bool_to_bv1

let slt_bool bv1 bv2 = !$$$BitVector.mk_slt ctx bv1 bv2

(** signed less or equal than *)
let sle bv1 bv2 = !$$$BitVector.mk_sle ctx bv1 bv2 |> bool_to_bv1

let sle_bool bv1 bv2 = !$$$BitVector.mk_sle ctx bv1 bv2

(** unsigned less than *)
let ult bv1 bv2 = !$$$BitVector.mk_ult ctx bv1 bv2 |> bool_to_bv1

let ult_bool bv1 bv2 = !$$$BitVector.mk_ult ctx bv1 bv2

(** unsigned less or equal than *)
let ule bv1 bv2 = !$$$BitVector.mk_ule ctx bv1 bv2 |> bool_to_bv1

let ule_bool bv1 bv2 = !$$$BitVector.mk_ule ctx bv1 bv2

(** unsigned greater than *)
let ugt bv1 bv2 = !$$$BitVector.mk_ugt ctx bv1 bv2 |> bool_to_bv1

let ugt_bool bv1 bv2 = !$$$BitVector.mk_ugt ctx bv1 bv2
let concat bv1 bv2 = !$$$BitVector.mk_concat ctx bv1 bv2

let sext bv ~size =
  let* ctx = read () in
  let* bv = bv in
  return (BitVector.mk_sign_ext ctx size bv)

let zext bv ~size =
  let* ctx = read () in
  let* bv = bv in
  return (BitVector.mk_zero_ext ctx size bv)

let extract ~high ~low bv =
  let* ctx = read () in
  let* bv = bv in
  return (BitVector.mk_extract ctx high low bv)
