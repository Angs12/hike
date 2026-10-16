(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

(* The domain's numeric substrate, a drop-in for [Bap.Std.Word].  A
   value has exactly one representation, chosen by its magnitude and its
   declared width: [Small] carries a payload below 2^62 as an immediate,
   [W64] a payload in [2^62, 2^64) at width <= 64 as an [int64] bit
   pattern, and [Big] a payload of 2^62 or more at width > 64 as a
   [Z.t].  Each arm computes the same function, so moving between them
   is exact.  A value is the canonical payload of BAP's representation:
   [0 <= v < 2^width], with the signed flag carried beside it; arithmetic
   results are unsigned, because BAP packs them unsigned. *)

open Bap.Std

(* value, width, signed *)
type t =
  | Small of int * int * bool
  | W64 of int64 * int * bool
  | Big of Z.t * int * bool

let[@inline] bitwidth (t : t) : int =
  match t with Small (_, w, _) | W64 (_, w, _) | Big (_, w, _) -> w

let[@inline] is_signed (t : t) : bool =
  match t with Small (_, _, s) | W64 (_, _, s) | Big (_, _, s) -> s

let[@inline] signed (t : t) : t =
  match t with
  | Small (_, _, true) | W64 (_, _, true) | Big (_, _, true) -> t
  | Small (v, w, _) -> Small (v, w, true)
  | W64 (x, w, _) -> W64 (x, w, true)
  | Big (z, w, _) -> Big (z, w, true)

let[@inline] unsigned (t : t) : t =
  match t with
  | Small (_, _, false) | W64 (_, _, false) | Big (_, _, false) -> t
  | Small (v, w, _) -> Small (v, w, false)
  | W64 (x, w, _) -> W64 (x, w, false)
  | Big (z, w, _) -> Big (z, w, false)

let[@inline] to_z (t : t) : Z.t =
  match t with
  | Small (v, _, _) -> Z.of_int v
  | W64 (x, _, _) -> Z.of_int64_unsigned x
  | Big (z, _, _) -> z

(* The low 64 bits.  Exact for [Small] and [W64]; the int64 lanes below
   never read a [Big]. *)
let[@inline] to_i64 (t : t) : int64 =
  match t with
  | Small (v, _, _) -> Int64.of_int v
  | W64 (x, _, _) -> x
  | Big (z, _, _) -> Z.to_int64_unsigned (Z.extract z 0 64)

(* Masks to [w] bits.  [max_int] is a no-op for [w >= 62]: a [Small] payload
   is already below 2^62 <= 2^w there. *)
let[@inline] mask (w : int) : int =
  if w >= 62 then max_int else if w <= 0 then 0 else (1 lsl w) - 1

let[@inline] mask64 (w : int) : int64 =
  if w >= 64 then (-1L) else if w <= 0 then 0L else Int64.pred (Int64.shift_left 1L w)

(* 2^w - 1. *)
let zmax (w : int) : Z.t = Z.sub (Z.shift_left Z.one w) Z.one

(* The canonical value of an unsigned 64-bit pattern already below 2^w. *)
let[@inline] mk64 (x : int64) (w : int) (s : bool) : t =
  if Int64.equal (Int64.shift_right_logical x 62) 0L then Small (Int64.to_int x, w, s)
  else if w <= 64 then W64 (x, w, s)
  else Big (Z.of_int64_unsigned x, w, s)

(* Reduces a 64-bit result to [w <= 64] bits. *)
let[@inline] red64 (x : int64) (w : int) : t = mk64 (Int64.logand x (mask64 w)) w false

(* Reduces to [0, 2^w) and picks the canonical arm. *)
let[@inline] mkzw (z : Z.t) (w : int) (s : bool) : t =
  let z = if Z.sign z >= 0 && Z.numbits z <= w then z else Z.logand z (zmax w) in
  if Z.fits_int z then Small (Z.to_int z, w, s)
  else if w <= 64 then W64 (Z.to_int64_unsigned z, w, s)
  else Big (z, w, s)

let[@inline] mkz (z : Z.t) (w : int) : t = mkzw z w false

let of_z = mkz

(* The int64 lane serves every operation at [w <= 64] whose operands
   carry no [Big] (a [Big] operand has a mismatched width). *)
let[@inline] lane64 (w : int) (b : t) : bool =
  w <= 64 && (match b with Big _ -> false | Small _ | W64 _ -> true)

let make_ones (w : int) : t =
  if w <= 62 then Small (mask w, w, false)
  else if w <= 64 then W64 (mask64 w, w, false)
  else mkz (zmax w) w

(* The per-width constants, shared below [const_widths] so the [==] fast
   paths hit; values are immutable, so sharing is unobservable. *)
let const_widths = 257
let zeros_tbl : t array = Array.init const_widths (fun w -> Small (0, w, false))
let ones_tbl : t array = Array.init const_widths make_ones
let one_tbl : t array =
  Array.init const_widths (fun w -> Small ((if w <= 0 then 0 else 1), w, false))

let[@inline] zero (w : int) : t =
  if w >= 0 && w < const_widths then Array.unsafe_get zeros_tbl w else Small (0, w, false)

let[@inline] one (w : int) : t =
  if w >= 0 && w < const_widths then Array.unsafe_get one_tbl w
  else if w <= 0 then Small (0, w, false)
  else Small (1, w, false)

let[@inline] ones (w : int) : t =
  if w >= 0 && w < const_widths then Array.unsafe_get ones_tbl w else make_ones w

let b0 : t = zero 1
let b1 : t = one 1

let of_int ~width (v : int) : t =
  if width <= 62 then Small (v land mask width, width, false)
  else if v >= 0 then Small (v, width, false)
  else if width <= 64 then red64 (Int64.of_int v) width
  else mkz (Z.add (Z.shift_left Z.one width) (Z.of_int v)) width

let of_int64 ?(width = 64) (v : int64) : t =
  if Int64.compare v 0L >= 0 && Int64.compare v (Int64.of_int max_int) <= 0 then
    Small (Int64.to_int v land mask width, width, false)
  else if width <= 64 then red64 v width
  else of_z (Z.of_int64 v) width

let[@inline] is_zero (t : t) : bool =
  match t with Small (v, _, _) -> v = 0 | W64 _ -> false | Big (z, _, _) -> Z.sign z = 0

let[@inline] is_one (t : t) : bool =
  match t with Small (v, _, _) -> v = 1 | W64 _ -> false | Big (z, _, _) -> Z.equal z Z.one

(* Bit [w-1]; always [false] for a [Small] at [w > 62], since its payload
   is below 2^62. *)
let msb (t : t) : bool =
  match t with
  | Small (v, w, _) -> w >= 1 && w <= 62 && v >= 1 lsl (w - 1)
  | W64 (x, w, _) -> Int64.equal (Int64.shift_right_logical x (w - 1)) 1L
  | Big (z, w, _) -> w >= 1 && Z.testbit z (w - 1)

let succ (t : t) : t =
  match t with
  | Small (v, w, _) ->
    if v < max_int then Small ((v + 1) land mask w, w, false)
    else if w <= 64 then red64 (Int64.succ (Int64.of_int v)) w
    else mkz (Z.succ (Z.of_int v)) w
  | W64 (x, w, _) -> red64 (Int64.succ x) w
  | Big (z, w, _) -> mkz (Z.succ z) w

let pred (t : t) : t =
  match t with
  | Small (v, w, _) ->
    if v > 0 then Small (v - 1, w, false)
    else ones w
  | W64 (x, w, _) -> mk64 (Int64.pred x) w false
  | Big (z, w, _) -> mkz (Z.pred z) w

let neg (t : t) : t =
  match t with
  | Small (v, w, _) when w <= 62 -> Small ((-v) land mask w, w, false)
  | (Small (_, w, _) | W64 (_, w, _)) when w <= 64 -> red64 (Int64.neg (to_i64 t)) w
  | _ -> mkz (Z.neg (to_z t)) (bitwidth t)

let lnot (t : t) : t =
  match t with
  | Small (v, w, _) when w <= 62 -> Small (lnot v land mask w, w, false)
  | (Small (_, w, _) | W64 (_, w, _)) when w <= 64 -> red64 (Int64.lognot (to_i64 t)) w
  | _ -> mkz (Z.lognot (to_z t)) (bitwidth t)

let add (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) when x <= max_int - y ->
    (* Payloads are non-negative, so [max_int - y] cannot overflow and
       [x <= max_int - y] is exactly "x + y stays in the int63 range". *)
    Small ((x + y) land mask w, w, false)
  | _ when lane64 w b -> red64 (Int64.add (to_i64 a) (to_i64 b)) w
  | _ -> mkz (Z.add (to_z a) (to_z b)) w

let sub (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) when x >= y || w <= 62 ->
    (* [x - y] cannot overflow; only a negative difference at [w > 62]
       leaves the immediate. *)
    Small ((x - y) land mask w, w, false)
  | _ when lane64 w b -> red64 (Int64.sub (to_i64 a) (to_i64 b)) w
  | _ -> mkz (Z.sub (to_z a) (to_z b)) w

let mul (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) when x < 0x4000_0000 && y < 0x4000_0000 ->
    (* Both below 2^30 keeps the product below 2^60. *)
    Small ((x * y) land mask w, w, false)
  | _ when lane64 w b -> red64 (Int64.mul (to_i64 a) (to_i64 b)) w
  | _ -> mkz (Z.mul (to_z a) (to_z b)) w

(* [Z.t] arms of the signed lanes: [Bitvec]'s [div]/[rem]/[smod] at [w]
   bits, with [y = 0] collapsing to [ones] (div) and [x] (rem). *)
let udiv_z (x : Z.t) (y : Z.t) (w : int) : Z.t =
  if Z.sign y = 0 then zmax w else Z.logand (Z.div x y) (zmax w)

let urem_z (x : Z.t) (y : Z.t) (w : int) : Z.t =
  if Z.sign y = 0 then x else Z.logand (Z.rem x y) (zmax w)

let negz (z : Z.t) (w : int) : Z.t = Z.logand (Z.neg z) (zmax w)

let msb_z (z : Z.t) (w : int) : bool = w >= 1 && Z.testbit z (w - 1)

(* The same arms on unsigned 64-bit patterns at [w <= 64]. *)
let udiv64 (x : int64) (y : int64) (w : int) : int64 =
  if Int64.equal y 0L then mask64 w else Int64.unsigned_div x y

let urem64 (x : int64) (y : int64) : int64 =
  if Int64.equal y 0L then x else Int64.unsigned_rem x y

let neg64 (x : int64) (w : int) : int64 = Int64.logand (Int64.neg x) (mask64 w)

let msb64 (x : int64) (w : int) : bool =
  w >= 1 && Int64.equal (Int64.logand (Int64.shift_right_logical x (w - 1)) 1L) 1L

(* The signed lanes fire on the SIGNED FLAG, not on [msb]: BAP dispatches
   [sdiv]/[srem] when either operand is signed, and an unsigned word with
   its top bit set divides unsigned. *)
let div (a : t) (b : t) : t =
  let w = bitwidth a in
  let signed = is_signed a || is_signed b in
  match a, b with
  | Small (x, _, _), Small (y, _, _) when not signed ->
    if y = 0 then ones w else Small (x / y, w, false)
  | _ when lane64 w b ->
    let x = to_i64 a and y = to_i64 b in
    let r =
      if not signed then udiv64 x y w
      else
        match msb64 x w, msb64 y w with
        | false, false -> udiv64 x y w
        | true, false -> neg64 (udiv64 (neg64 x w) y w) w
        | false, true -> neg64 (udiv64 x (neg64 y w) w) w
        | true, true -> udiv64 (neg64 x w) (neg64 y w) w
    in
    mk64 r w false
  | _ ->
    let x = to_z a and y = to_z b in
    let r =
      if not signed then udiv_z x y w
      else
        match msb_z x w, msb_z y w with
        | false, false -> udiv_z x y w
        | true, false -> negz (udiv_z (negz x w) y w) w
        | false, true -> negz (udiv_z x (negz y w) w) w
        | true, true -> udiv_z (negz x w) (negz y w) w
    in
    mkz r w

let modulo (a : t) (b : t) : t =
  let w = bitwidth a in
  let signed = is_signed a || is_signed b in
  match a, b with
  | Small (x, _, _), Small (y, _, _) when not signed ->
    if y = 0 then Small (x, w, false) else Small (x mod y, w, false)
  | _ when lane64 w b ->
    let x = to_i64 a and y = to_i64 b in
    let r =
      if not signed then urem64 x y
      else
        match msb64 x w, msb64 y w with
        | false, false -> urem64 x y
        | true, false -> neg64 (urem64 (neg64 x w) y) w
        | false, true -> neg64 (urem64 x (neg64 y w)) w
        | true, true -> neg64 (urem64 (neg64 x w) (neg64 y w)) w
    in
    red64 r w
  | _ ->
    let x = to_z a and y = to_z b in
    let r =
      if not signed then urem_z x y w
      else
        match msb_z x w, msb_z y w with
        | false, false -> urem_z x y w
        | true, false -> negz (urem_z (negz x w) y w) w
        | false, true -> negz (urem_z x (negz y w) w) w
        | true, true -> negz (urem_z (negz x w) (negz y w) w) w
    in
    mkz r w

let logand (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) -> Small (x land y land mask w, w, false)
  | _ when lane64 w b -> red64 (Int64.logand (to_i64 a) (to_i64 b)) w
  | _ -> mkz (Z.logand (to_z a) (to_z b)) w

let logor (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) -> Small (x lor y land mask w, w, false)
  | _ when lane64 w b -> red64 (Int64.logor (to_i64 a) (to_i64 b)) w
  | _ -> mkz (Z.logor (to_z a) (to_z b)) w

let logxor (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) -> Small (x lxor y land mask w, w, false)
  | _ when lane64 w b -> red64 (Int64.logxor (to_i64 a) (to_i64 b)) w
  | _ -> mkz (Z.logxor (to_z a) (to_z b)) w

(* A shift amount; a non-[Small] amount is at least 2^62, past any width. *)
let[@inline] shift_amount (b : t) : int =
  match b with Small (n, _, _) -> n | W64 _ | Big _ -> max_int

(* [n >= w] is BAP's overshift arm: it overshifts at
   [n >= numbits (2^w - 1)], which is [w]. *)
let lshift (a : t) (b : t) : t =
  let w = bitwidth a and n = shift_amount b in
  if n >= w then zero w
  else
    match a with
    (* [x < 2^(62-n)] is exactly "x lsl n stays in the int63 range". *)
    | Small (x, _, _) when n < 62 && x lsr (62 - n) = 0 -> Small (x lsl n land mask w, w, false)
    | (Small _ | W64 _) when w <= 64 -> red64 (Int64.shift_left (to_i64 a) n) w
    | _ -> mkz (Z.shift_left (to_z a) n) w

(* 2^n at [width] bits. *)
let pow2 ~(width : int) (n : int) : t =
  lshift (one width) (of_int ~width n)

let rshift (a : t) (b : t) : t =
  let w = bitwidth a and n = shift_amount b in
  if n >= w then zero w
  else
    match a with
    | Small (x, _, _) -> if n >= 62 then zero w else Small (x lsr n, w, false)
    | W64 (x, _, _) -> mk64 (Int64.shift_right_logical x n) w false
    | Big (z, _, _) -> mkz (Z.shift_right z n) w

let arshift (a : t) (b : t) : t =
  let w = bitwidth a and n = shift_amount b in
  let s = msb a in
  if n >= w then (if s then ones w else zero w)
  else
    match a with
    | Small (x, _, _) when w <= 62 ->
      (* Sign fill is the top [n] bits: [mask w] minus [mask (w - n)]. *)
      let fill = if s then mask w lxor mask (w - n) else 0 in
      Small ((x lsr n) lor fill land mask w, w, false)
    | (Small _ | W64 _) when w <= 64 ->
      (* Move bit [w-1] to bit 63, then shift arithmetically back past it. *)
      let up = 64 - w in
      red64 (Int64.shift_right (Int64.shift_left (to_i64 a) up) (up + n)) w
    | _ ->
      let x = to_z a in
      let r = Z.shift_right x n in
      if s then mkz (Z.logor (Z.shift_left (zmax w) (w - n)) r) w else mkz r w

(* BAP's order: width first, then the payload, with the two's-complement
   order when either side is signed. *)
let compare (a : t) (b : t) : int =
  let c = Stdlib.compare (bitwidth a) (bitwidth b) in
  if c <> 0 then c
  else begin
    let u =
      match a, b with
      | Small (x, _, _), Small (y, _, _) -> Stdlib.compare x y
      | (Small _ | W64 _), (Small _ | W64 _) -> Int64.unsigned_compare (to_i64 a) (to_i64 b)
      | _ -> Z.compare (to_z a) (to_z b)
    in
    if is_signed a || is_signed b then
      match msb a, msb b with
      | true, false -> -1
      | false, true -> 1
      | _ -> u
    else u
  end

let equal (a : t) (b : t) : bool = compare a b = 0

let min (a : t) (b : t) : t = if compare a b < 0 then a else b
let max (a : t) (b : t) : t = if compare a b > 0 then a else b

let extract_exn ?hi ?(lo = 0) (t : t) : t =
  let w = bitwidth t in
  let hi = Option.value hi ~default:(w - 1) in
  let len = hi - lo + 1 in
  if len <= 0 then failwith "Cbat_word.extract: negative length";
  (* BAP sign-extends a signed source, and the extension vanishes when the
     result is reduced to [len] bits, so every arm is the plain slice. *)
  match t with
  | Small (v, _, _) -> Small ((if lo >= 62 then 0 else v lsr lo) land mask len, len, false)
  | W64 (x, _, _) ->
    let x = if lo >= 64 then 0L else Int64.shift_right_logical x lo in
    mk64 (Int64.logand x (mask64 len)) len false
  | Big (z, _, _) -> mkz (Z.extract z lo len) len

(* BIL cast to [sz] bits: HIGH reads the top bits, SIGNED sign-extends. *)
let cast (ct : Bil.cast) (sz : int) (t : t) : t =
  let w = bitwidth t in
  match ct with
  | Bil.UNSIGNED | Bil.LOW -> extract_exn ~hi:(sz - 1) t
  | Bil.SIGNED when sz <= w -> signed (extract_exn ~hi:(sz - 1) t)
  (* Sign-extend from the operand's own width: extracting at [sz]
     zero-fills the high bits and the sign re-read lands on bit [sz-1]
     instead of bit [w-1]. *)
  | Bil.SIGNED when sz <= 64 && w >= 1 ->
    let up = 64 - w in
    signed (red64 (Int64.shift_right (Int64.shift_left (to_i64 t) up) up) sz)
  | Bil.SIGNED ->
    let bits = to_z t in
    let bits = if Z.testbit bits (w - 1)
      then Z.logor bits (Z.shift_left Z.minus_one (w - 1))
      else bits in
    signed (mkz bits sz)
  | Bil.HIGH -> extract_exn ~lo:(w - sz) t

let concat (a : t) (b : t) : t =
  let wb = bitwidth b in
  let w = bitwidth a + wb in
  match a, b with
  | Small (x, _, _), Small (y, _, _) when w <= 62 ->
    Small (x lsl wb lor y land mask w, w, false)
  | (Small _ | W64 _), (Small _ | W64 _) when w <= 64 && wb < 64 ->
    red64 (Int64.logor (Int64.shift_left (to_i64 a) wb) (to_i64 b)) w
  | _ -> mkz (Z.logor (Z.shift_left (to_z a) wb) (to_z b)) w

let rec gcd_int (a : int) (b : int) : int = if b = 0 then a else gcd_int b (a mod b)

let rec gcd64 (a : int64) (b : int64) : int64 =
  if Int64.equal b 0L then a else gcd64 b (Int64.unsigned_rem a b)

let gcd_exn (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) ->
    if x = 0 then Small (y, w, false)
    else if y = 0 then Small (x, w, false)
    else Small (gcd_int x y land mask w, w, false)
  | _ when lane64 w b -> red64 (gcd64 (to_i64 a) (to_i64 b)) w
  | _ -> mkz (Z.gcd (to_z a) (to_z b)) w

let lcm_exn (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) ->
    if x = 0 || y = 0 then zero w
    else begin
      let q = x / gcd_int x y in
      if q <= max_int / y then Small (q * y land mask w, w, false)
      else mkz (Z.lcm (Z.of_int x) (Z.of_int y)) w
    end
  | _ -> mkz (Z.lcm (to_z a) (to_z b)) w

(* Bezout coefficients are signed and unbounded on the way, so there is no
   machine-int arm. *)
let gcdext_exn (a : t) (b : t) : t * t * t =
  let w = bitwidth a in
  let x = to_z a and y = to_z b in
  let g, u, v =
    if Z.sign x = 0 then y, Z.zero, Z.one
    else if Z.sign y = 0 then x, Z.one, Z.zero
    else Z.gcdext x y
  in
  mkz g w, mkz u w, mkz v w

(* Hex above 9, decimal below, as [Word]'s default printer does. *)
let to_string (t : t) : string =
  let w = bitwidth t and s = is_signed t in
  let z = to_z t in
  let neg = s && msb t in
  let v = if neg then Z.sub (Z.shift_left Z.one w) z else z in
  let digits = if Z.lt v (Z.of_int 10) then Z.to_string v else "0x" ^ Z.format "%X" v in
  Printf.sprintf "%s%s:%d%c" (if neg then "-" else "") digits w (if s then 's' else 'u')

let of_string (str : string) : t =
  match String.split_on_char ':' str with
  | [ v; m ] ->
    let n = String.length m in
    let s = n > 0 && m.[n - 1] = 's' in
    let u = n > 0 && m.[n - 1] = 'u' in
    let w = Stdlib.int_of_string (if s || u then String.sub m 0 (n - 1) else m) in
    mkzw (Z.of_string v) w s
  | _ -> failwith (Printf.sprintf "Cbat_word.of_string: '%s'" str)

(* [Bitvec.convert]: a value above [max_signed] is read as its [size]-bit
   two's complement, and one above [max_unsigned] does not fit. *)
let to_int_exn (t : t) : int =
  match t with
  | Small (v, _, _) -> v
  | W64 (x, _, _) when Int64.compare x 0L >= 0 -> Int64.to_int x
  | Big (z, _, _) when Z.numbits z <= Sys.int_size -> Z.to_int (Z.signed_extract z 0 Sys.int_size)
  | _ -> failwith (Printf.sprintf "%s doesn't fit the int type" (to_string t))

let to_int_sat (t : t) : int =
  match t with Small (v, _, _) -> v | W64 _ | Big _ -> max_int

(* The fitting cases answer directly; only a failure pays for [try_with]. *)
let to_int (t : t) : int Core.Or_error.t =
  match t with
  | Small (v, _, _) -> Ok v
  | W64 (x, _, _) when Int64.compare x 0L >= 0 -> Ok (Int64.to_int x)
  | _ -> Core.Or_error.try_with (fun () -> to_int_exn t)

let to_int64_exn (t : t) : int64 =
  match t with
  | Small (v, _, _) -> Int64.of_int v
  | W64 (x, _, _) -> x
  | Big (z, _, _) when Z.numbits z <= 64 -> Z.to_int64_unsigned z
  | Big _ -> failwith (Printf.sprintf "%s doesn't fit the int64 type" (to_string t))

let to_int64 (t : t) : int64 Core.Or_error.t =
  match t with
  | Small (v, _, _) -> Ok (Int64.of_int v)
  | W64 (x, _, _) -> Ok x
  | Big _ -> Core.Or_error.try_with (fun () -> to_int64_exn t)

let le_int64 (bytes : Bytes.t) ~(off : int) ~(len : int) : int64 =
  let b k =
    if off + k < Bytes.length bytes
    then Int64.of_int (Char.code (Bytes.get bytes (off + k)))
    else 0L
  in
  let rec go acc k =
    if k = len then acc
    else go (Int64.logor acc (Int64.shift_left (b k) (8 * k))) (k + 1)
  in
  go 0L 0

let to_int64_opt (t : t) : int64 option =
  match t with
  | Small (v, _, _) -> Some (Int64.of_int v)
  | W64 (x, _, _) -> Some x
  | Big (z, _, _) when Z.numbits z <= 64 -> Some (Z.to_int64_unsigned z)
  | Big _ -> None

let int64_pair (lo : t) (hi : t) : (int64 * int64) option =
  match to_int64_opt lo, to_int64_opt hi with
  | Some lo, Some hi -> Some (lo, hi)
  | _ -> None

let pp (ppf : Format.formatter) (t : t) : unit = Format.fprintf ppf "%s" (to_string t)

(* The BAP<->VSA boundary moves BITS through [Bitvec]'s bignum
   conversions — no strings, at every width.  [mkzw] re-normalizes the
   word's value into the canonical [0,2^w); [bigint_unsafe] requires a
   value already in that range, which [v] is by construction. *)
let of_word (w : word) : t =
  mkzw (Bitvec.to_bigint (Word.to_bitvec w)) (Word.bitwidth w) false

(* The payload is already the two's-complement bit pattern; the sign
   flag rides on the BAP word so a signed value keeps its reading. *)
let to_word (t : t) : word =
  let word = Word.create (Bitvec.bigint_unsafe (to_z t)) (bitwidth t) in
  if is_signed t then Word.signed word else word

let sexp_of_t (t : t) : Core.Sexp.t = Core.Sexp.Atom (to_string t)

let t_of_sexp (s : Core.Sexp.t) : t =
  match s with
  | Core.Sexp.Atom a -> of_string a
  | _ -> failwith "Cbat_word.t_of_sexp: expects an atom"

module Stringable = struct
  type nonrec t = t

  let to_string = to_string
  let of_string = of_string
end

include Core.Binable.Of_stringable_with_uuid (struct
  include Stringable

  let caller_identity = Bin_prot.Shape.Uuid.of_string "hike:cbat_word.t/1"
end)

(* The word-op set, in terms of the ops above. *)

let mul_exact (a : t) (b : t) : t =
  let w = bitwidth a + bitwidth b in
  mul (extract_exn ~hi:(w - 1) a) (extract_exn ~hi:(w - 1) b)

let add_exact (a : t) (b : t) : t =
  let w = 1 + Stdlib.max (bitwidth a) (bitwidth b) in
  add (extract_exn ~hi:(w - 1) a) (extract_exn ~hi:(w - 1) b)

let succ_exact (a : t) : t = succ (extract_exn ~hi:(bitwidth a) a)

let lshift_exact (a : t) (i : int) : t =
  let w = i + bitwidth a in
  lshift (extract_exn ~hi:(w - 1) a) (of_int ~width:w i)

(* Not total: callers must pass equal widths. *)
let bounded_gcd (a : t) (b : t) : t =
  let w = bitwidth a in
  assert (w = bitwidth b);
  if is_zero a then b else if is_zero b then a else gcd_exn a b

(* Least non-negative (x, y) with ax + by = c.  Not total: equal widths. *)
let bounded_diophantine (a : t) (b : t) (c : t) : (t * t) option =
  let size = bitwidth a in
  assert (size = bitwidth b);
  assert (size = bitwidth c);
  let z = zero size in
  if is_zero c then Some (z, z)
  else if is_zero a && is_zero b then None
  else if is_zero a then
    if is_zero (modulo c b) then Some (z, div c b) else None
  else if is_zero b then
    if is_zero (modulo c a) then Some (div c a, z) else None
  else begin
    let d, ux, uy = gcdext_exn a b in
    if not (is_zero (modulo c d)) then None
    else
      let sx = signed ux and sy = signed uy in
      let q = div c d in
      let x0 = signed (mul_exact sx q) and y0 = signed (mul_exact sy q) in
      Some (extract_exn ~hi:(size - 1) x0, extract_exn ~hi:(size - 1) y0)
  end

(* Trailing-zero count of a positive immediate. *)
let trailing_zeros_int (v : int) : int =
  let rec go (v : int) (k : int) : int =
    if v land 0xFFFF_FFFF = 0 then go (v lsr 32) (k + 32)
    else if v land 0xFFFF = 0 then go (v lsr 16) (k + 16)
    else if v land 0xFF = 0 then go (v lsr 8) (k + 8)
    else if v land 0xF = 0 then go (v lsr 4) (k + 4)
    else if v land 0x3 = 0 then go (v lsr 2) (k + 2)
    else if v land 0x1 = 0 then k + 1
    else k
  in
  go v 0

(* Highest set-bit position of a positive immediate. *)
let highest_bit_int (v : int) : int =
  let rec go (v : int) (k : int) : int =
    if v lsr 32 <> 0 then go (v lsr 32) (k + 32)
    else if v lsr 16 <> 0 then go (v lsr 16) (k + 16)
    else if v lsr 8 <> 0 then go (v lsr 8) (k + 8)
    else if v lsr 4 <> 0 then go (v lsr 4) (k + 4)
    else if v lsr 2 <> 0 then go (v lsr 2) (k + 2)
    else if v lsr 1 <> 0 then k + 1
    else k
  in
  go v 0

(* Splits into the odd part and the power of two.  The search reads the
   payload directly: an immediate's bits through the int helpers, a
   bignum's through [Z.trailing_zeros]/[Z.extract]. *)
let factor_2s (t : t) : t * int =
  let w = bitwidth t in
  match t with
  | Small (v, _, _) ->
    if v = 0 then (zero w, w - 1)
    else
      let lo = trailing_zeros_int v in
      (Small ((v lsr lo) land mask w, w, false), lo)
  | W64 (x, _, _) ->
    (* [x] is nonzero; its low 63 bits are zero only at 2^63. *)
    let low = Int64.to_int x in
    let lo = if low = 0 then 63 else trailing_zeros_int low in
    (mk64 (Int64.shift_right_logical x lo) w false, lo)
  | Big (z, _, _) ->
    if Z.sign z = 0 then (zero w, w - 1)
    else
      let lo = Z.trailing_zeros z in
      (mkz (Z.extract z lo w) w, lo)

(* The domain size 2^i at [width] bits; i >= width truncates to 0
   (Word.lshift semantics).  Production call sites always pass
   i < width. *)
let dom_size ?width (i : int) : t =
  let wd = Option.value width ~default:(i + 1) in
  if i < 0 then zero wd
  else
    let i' = i land ((1 lsl (Stdlib.min wd 62)) - 1) in
    if i' >= wd then zero wd
    else if i' = 0 then one wd
    else if i' <= 61 then Small (1 lsl i', wd, false)
    else if i' <= 63 then mk64 (Int64.shift_left 1L i') wd false
    else mkz (Z.shift_left Z.one i') wd

(* 2^(width-1) at [width] bits. *)
let half (w : int) : t = dom_size ~width:w (w - 1)

let cap_at_width ~width (t : t) : t =
  let w = bitwidth t in
  if w = width then t
  else if w < width then extract_exn ~hi:(width - 1) t
  else extract_exn ~hi:(width - 1) (min (pred (dom_size ~width:w width)) t)

(* Extend by one high bit. *)
let add_bit (w : t) : t =
  extract_exn ~hi:(bitwidth w) w

(* Position of the leading 1-bit. *)
let lead_1_bit (w : t) : int option =
  if is_zero w then None
  else
    match w with
    | Small (v, _, _) -> Some (highest_bit_int v)
    | W64 (x, _, _) -> Some (if Int64.compare x 0L < 0 then 63 else 62)
    | Big (z, _, _) -> Some (Z.numbits z - 1)

let count_initial_1s (w : t) : int = snd @@ factor_2s @@ lnot w

let endian_string : Word.endian -> string = function
  | BigEndian -> "BE"
  | LittleEndian -> "LE"

(* [compare w (of_int ~width i)] without building the word when [i] needs
   no wrapping to [w]'s width and [w] is an unsigned machine word. *)
let compare_int (w : t) (i : int) : int =
  match w with
  | Small (x, n, false) when i >= 0 && (n > 62 || i lsr n = 0) ->
    Stdlib.compare x i
  | W64 (x, n, false) when i >= 0 && (n > 62 || i lsr n = 0) ->
    Int64.unsigned_compare x (Int64.of_int i)
  | _ -> compare w (of_int ~width:(bitwidth w) i)

let gt_int (w : t) (i : int) : bool = compare_int w i > 0

let leq_int (w : t) (i : int) : bool = compare_int w i <= 0

(* Ordered infixes, defined last so the module's own uses of the
   Stdlib operators stay in scope. *)
let ( = ) (a : t) (b : t) : bool = compare a b = 0
let ( <> ) (a : t) (b : t) : bool = compare a b <> 0
let ( < ) (a : t) (b : t) : bool = compare a b < 0
let ( > ) (a : t) (b : t) : bool = compare a b > 0
let ( <= ) (a : t) (b : t) : bool = compare a b <= 0
let ( >= ) (a : t) (b : t) : bool = compare a b >= 0
