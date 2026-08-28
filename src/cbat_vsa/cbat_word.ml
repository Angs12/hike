open Bap.Std
module W0 = Word
include Word
let to_i64 w = W0.to_int64_exn w
let of_i64 ~width v = W0.of_int64 ~width v
let add a b =
  let wa = W0.bitwidth a and wb = W0.bitwidth b in
  if Stdlib.(wa <= 64 && wb <= 64 && wa = wb) then
    of_i64 ~width:wa Int64.(add (to_i64 a) (to_i64 b))
  else W0.add a b
let sub a b =
  let wa = W0.bitwidth a and wb = W0.bitwidth b in
  if Stdlib.(wa <= 64 && wb <= 64 && wa = wb) then
    of_i64 ~width:wa Int64.(sub (to_i64 a) (to_i64 b))
  else W0.sub a b
let mul a b =
  let wa = W0.bitwidth a and wb = W0.bitwidth b in
  if Stdlib.(wa <= 64 && wb <= 64 && wa = wb) then
    of_i64 ~width:wa Int64.(mul (to_i64 a) (to_i64 b))
  else W0.mul a b
let div a b =
  let wa = W0.bitwidth a and wb = W0.bitwidth b in
  if Stdlib.(wa <= 64 && wb <= 64 && wa = wb) then
    let av = to_i64 a and bv = to_i64 b in
    if Stdlib.(bv = 0L) then W0.div a b
    else if Stdlib.(av < 0L || bv < 0L) then W0.div a b
    else of_i64 ~width:wa Int64.(div av bv)
  else W0.div a b
let modulo a b =
  let wa = W0.bitwidth a and wb = W0.bitwidth b in
  if Stdlib.(wa <= 64 && wb <= 64 && wa = wb) then
    let av = to_i64 a and bv = to_i64 b in
    if Stdlib.(bv = 0L) then W0.modulo a b
    else if Stdlib.(av < 0L || bv < 0L) then W0.modulo a b
    else of_i64 ~width:wa Int64.(rem av bv)
  else W0.modulo a b
