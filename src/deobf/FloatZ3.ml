module FloatingPoint = Z3.FloatingPoint
open Monads.Std.Monad.Reader

let ctx : (Z3.context, Z3.context) Monads.Std.Monad.Reader.reader = read ()
let round_positive = !$FloatingPoint.RoundingMode.mk_round_toward_positive ctx
let round_negative = !$FloatingPoint.RoundingMode.mk_round_toward_negative ctx
let round_zero = !$FloatingPoint.RoundingMode.mk_round_toward_zero ctx

let round_nearest =
  !$FloatingPoint.RoundingMode.mk_round_nearest_ties_to_even ctx

(** float equal *)
let ( #== ) expr1 expr2 = !$$$FloatingPoint.mk_eq ctx expr1 expr2

(** float add *)
let ( ++ ) expr1 expr2 = !$$$$FloatingPoint.mk_add ctx round_nearest expr1 expr2

(** float div *)
let ( // ) expr1 expr2 = !$$$$FloatingPoint.mk_div ctx round_nearest expr1 expr2

(** float mul *)
let ( @@ ) expr1 expr2 = !$$$$FloatingPoint.mk_mul ctx round_nearest expr1 expr2

(**float greater than *)
let ( >> ) expr1 expr2 = !$$$FloatingPoint.mk_gt ctx expr1 expr2

(**float greater or equal than *)
let ( >= ) expr1 expr2 = !$$$FloatingPoint.mk_geq ctx expr1 expr2

(**float less than *)
let ( << ) expr1 expr2 = !$$$FloatingPoint.mk_lt ctx expr1 expr2

(** float less or equal than *)
let ( =< ) expr1 expr2 = !$$$FloatingPoint.mk_leq ctx expr1 expr2

(** float sub *)
let ( -- ) expr1 expr2 = !$$$$FloatingPoint.mk_sub ctx round_nearest expr1 expr2

let float_sort ~exponent ~significand =
  let* ctx = read () in
  return (FloatingPoint.mk_sort ctx exponent significand)

let const_float identifier ~sort =
  let* ctx = read () in
  let* sort = sort in
  return (FloatingPoint.mk_const_s ctx identifier sort)

let imediate num ~sort =
  let* ctx = read () in
  let* sort = sort in
  return (FloatingPoint.mk_numeral_f ctx num sort)
