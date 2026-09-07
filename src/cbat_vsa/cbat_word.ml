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

(* The domain's numeric substrate, a drop-in for [Bap.Std.Word].

   [Small] carries an int63 immediate, [Big] a [Z.t]; the split is by VALUE
   MAGNITUDE, never by declared width, so a 129-bit word holding 3 is
   [Small].  Each op computes in machine ints when both operands are
   [Small] and the result stays in the int63 range, and in [Z.t] otherwise.
   The [Z.t] arm is the same operation at arbitrary precision, so falling
   back is exact, never an approximation.

   A value is the canonical payload of BAP's representation: [0 <= v <
   2^width], with the signed flag carried beside it.  Arithmetic results are
   unsigned, because BAP packs them unsigned. *)

open Bap.Std

(* value, width, signed *)
type t = Small of int * int * bool | Big of Z.t * int * bool

let[@inline] bitwidth (t : t) : int =
  match t with Small (_, w, _) -> w | Big (_, w, _) -> w

let[@inline] is_signed (t : t) : bool =
  match t with Small (_, _, s) -> s | Big (_, _, s) -> s

let[@inline] signed (t : t) : t =
  match t with Small (v, w, _) -> Small (v, w, true) | Big (z, w, _) -> Big (z, w, true)

let[@inline] unsigned (t : t) : t =
  match t with Small (v, w, _) -> Small (v, w, false) | Big (z, w, _) -> Big (z, w, false)

let[@inline] to_z (t : t) : Z.t =
  match t with Small (v, _, _) -> Z.of_int v | Big (z, _, _) -> z

(* Masks to [w] bits.  [max_int] is a no-op for [w >= 62]: a [Small] payload
   is already below 2^62 <= 2^w there. *)
let[@inline] mask (w : int) : int =
  if w >= 62 then max_int else if w <= 0 then 0 else (1 lsl w) - 1

(* 2^w - 1. *)
let zmax (w : int) : Z.t = Z.sub (Z.shift_left Z.one w) Z.one

(* Reduces to [0, 2^w) and narrows back to [Small] when the result fits. *)
let[@inline] mkzw (z : Z.t) (w : int) (s : bool) : t =
  let z = if Z.sign z >= 0 && Z.numbits z <= w then z else Z.logand z (zmax w) in
  if Z.fits_int z then Small (Z.to_int z, w, s) else Big (z, w, s)

let[@inline] mkz (z : Z.t) (w : int) : t = mkzw z w false

let of_z (z : Z.t) (w : int) : t = mkzw z w false

let zero (w : int) : t = Small (0, w, false)
let one (w : int) : t = if w <= 0 then Small (0, w, false) else Small (1, w, false)
let ones (w : int) : t = if w <= 62 then Small (mask w, w, false) else mkz (zmax w) w
let b0 : t = zero 1
let b1 : t = one 1

let of_int ~width (v : int) : t =
  if width <= 62 then Small (v land mask width, width, false)
  else if v >= 0 then Small (v, width, false)
  else mkz (Z.add (Z.shift_left Z.one width) (Z.of_int v)) width

let of_int32 ?(width = 32) (v : int32) : t = of_int ~width (Int32.to_int v)
let of_int64 ?(width = 64) (v : int64) : t = of_z (Z.of_int64 v) width

let[@inline] is_zero (t : t) : bool =
  match t with Small (v, _, _) -> v = 0 | Big (z, _, _) -> Z.sign z = 0

let[@inline] is_one (t : t) : bool =
  match t with Small (v, _, _) -> v = 1 | Big (z, _, _) -> Z.equal z Z.one

(* Bit [w-1]; always [false] when [w > 62], since a [Small] payload is
   below 2^62. *)
let msb (t : t) : bool =
  match t with
  | Small (v, w, _) -> w >= 1 && w <= 62 && v >= 1 lsl (w - 1)
  | Big (z, w, _) -> w >= 1 && Z.testbit z (w - 1)

let[@inline] lsb (t : t) : bool =
  match t with Small (v, _, _) -> v land 1 = 1 | Big (z, _, _) -> Z.is_odd z

let succ (t : t) : t =
  match t with
  | Small (v, w, _) ->
    if v = max_int then mkz (Z.succ (Z.of_int v)) w
    else Small ((v + 1) land mask w, w, false)
  | Big (z, w, _) -> mkz (Z.succ z) w

let pred (t : t) : t =
  match t with
  | Small (v, w, _) ->
    if v > 0 then Small (v - 1, w, false)
    else if w <= 62 then Small (mask w, w, false)
    else mkz (Z.neg Z.one) w
  | Big (z, w, _) -> mkz (Z.pred z) w

let neg (t : t) : t =
  match t with
  | Small (v, w, _) when w <= 62 -> Small ((-v) land mask w, w, false)
  | Small (v, w, _) -> mkz (Z.neg (Z.of_int v)) w
  | Big (z, w, _) -> mkz (Z.neg z) w

let lnot (t : t) : t =
  match t with
  | Small (v, w, _) when w <= 62 -> Small (lnot v land mask w, w, false)
  | Small (v, w, _) -> mkz (Z.lognot (Z.of_int v)) w
  | Big (z, w, _) -> mkz (Z.lognot z) w

let abs (t : t) : t = if msb t then neg t else t

let add (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) ->
    (* Payloads are non-negative, so [max_int - y] cannot overflow and
       [x <= max_int - y] is exactly "x + y stays in the int63 range". *)
    if x <= max_int - y then Small ((x + y) land mask w, w, false)
    else mkz (Z.add (Z.of_int x) (Z.of_int y)) w
  | _ -> mkz (Z.add (to_z a) (to_z b)) w

let sub (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) ->
    let d = x - y in
    (* [d] cannot overflow; only a negative [d] at [w > 62] needs [Z.t]. *)
    if d >= 0 || w <= 62 then Small (d land mask w, w, false)
    else mkz (Z.sub (Z.of_int x) (Z.of_int y)) w
  | _ -> mkz (Z.sub (to_z a) (to_z b)) w

let mul (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) ->
    (* Both below 2^30 keeps the product below 2^60; the wider cases are
       exact but not worth an overflow division on the hot path. *)
    if x < 0x4000_0000 && y < 0x4000_0000 then Small ((x * y) land mask w, w, false)
    else mkz (Z.mul (Z.of_int x) (Z.of_int y)) w
  | _ -> mkz (Z.mul (to_z a) (to_z b)) w

(* [Z.t] arms of the signed lanes: [Bitvec]'s [div]/[rem]/[smod] at [w]
   bits, with [y = 0] collapsing to [ones] (div) and [x] (rem). *)
let udiv_z (x : Z.t) (y : Z.t) (w : int) : Z.t =
  if Z.sign y = 0 then zmax w else Z.logand (Z.div x y) (zmax w)

let urem_z (x : Z.t) (y : Z.t) (w : int) : Z.t =
  if Z.sign y = 0 then x else Z.logand (Z.rem x y) (zmax w)

let negz (z : Z.t) (w : int) : Z.t = Z.logand (Z.neg z) (zmax w)
let addz (x : Z.t) (y : Z.t) (w : int) : Z.t = Z.logand (Z.add x y) (zmax w)

let msb_z (z : Z.t) (w : int) : bool = w >= 1 && Z.testbit z (w - 1)

(* The signed lanes fire on the SIGNED FLAG, not on [msb]: BAP dispatches
   [sdiv]/[srem] when either operand is signed, and an unsigned word with
   its top bit set divides unsigned. *)
let div (a : t) (b : t) : t =
  let w = bitwidth a in
  if not (is_signed a || is_signed b) then
    match a, b with
    | Small (x, _, _), Small (y, _, _) -> if y = 0 then ones w else Small (x / y, w, false)
    | _ -> mkz (udiv_z (to_z a) (to_z b) w) w
  else begin
    let x = to_z a and y = to_z b in
    let r =
      match msb_z x w, msb_z y w with
      | false, false -> udiv_z x y w
      | true, false -> negz (udiv_z (negz x w) y w) w
      | false, true -> negz (udiv_z x (negz y w) w) w
      | true, true -> udiv_z (negz x w) (negz y w) w
    in
    mkz r w
  end

let modulo (a : t) (b : t) : t =
  let w = bitwidth a in
  if not (is_signed a || is_signed b) then
    match a, b with
    | Small (x, _, _), Small (y, _, _) ->
      if y = 0 then Small (x, w, false) else Small (x mod y, w, false)
    | _ -> mkz (urem_z (to_z a) (to_z b) w) w
  else begin
    let x = to_z a and y = to_z b in
    let r =
      match msb_z x w, msb_z y w with
      | false, false -> urem_z x y w
      | true, false -> negz (urem_z (negz x w) y w) w
      | false, true -> negz (urem_z x (negz y w) w) w
      | true, true -> negz (urem_z (negz x w) (negz y w) w) w
    in
    mkz r w
  end

(* Sign follows the divisor, as [Bitvec.smod] defines it. *)
let smodulo (a : t) (b : t) : t =
  let w = bitwidth a in
  let x = to_z a and y = to_z b in
  let u = urem_z x y w in
  let r =
    if Z.sign u = 0 then u
    else
      match msb_z x w, msb_z y w with
      | false, false -> u
      | true, false -> addz (negz u w) y w
      | false, true -> addz u y w
      | true, true -> negz u w
  in
  mkz r w

let logand (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) -> Small (x land y land mask w, w, false)
  | _ -> mkz (Z.logand (to_z a) (to_z b)) w

let logor (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) -> Small (x lor y land mask w, w, false)
  | _ -> mkz (Z.logor (to_z a) (to_z b)) w

let logxor (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) -> Small (x lxor y land mask w, w, false)
  | _ -> mkz (Z.logxor (to_z a) (to_z b)) w

(* Shifting by [n >= 62] would wrap the machine shift, so those go to
   [Z.t]; [n >= w] is BAP's overshift arm. *)
let lshift (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (n, _, _) ->
    (* BAP overshifts at [n >= numbits (2^w - 1)], which is [w]. *)
    if n >= w then zero w
    else if n >= 62 then mkz (Z.shift_left (Z.of_int x) n) w
    (* [x < 2^(62-n)] is exactly "x lsl n stays in the int63 range". *)
    else if x lsr (62 - n) = 0 then Small (x lsl n land mask w, w, false)
    else mkz (Z.shift_left (Z.of_int x) n) w
  | _ ->
    let n = to_z b in
    if Z.fits_int n && Z.to_int n < w then mkz (Z.shift_left (to_z a) (Z.to_int n)) w
    else zero w

let rshift (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (n, _, _) ->
    if n >= 62 then zero w else Small (x lsr n land mask w, w, false)
  | _ ->
    let n = to_z b in
    if Z.fits_int n && Z.to_int n < w then mkz (Z.shift_right (to_z a) (Z.to_int n)) w
    else zero w

let arshift (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (n, _, _) when w <= 62 ->
    let s = msb a in
    if n >= 62 || n >= w then (if s then ones w else zero w)
    else begin
      (* Sign fill is the top [n] bits: [mask w] minus [mask (w - n)]. *)
      let fill = if s then mask w lxor mask (w - n) else 0 in
      Small ((x lsr n) lor fill land mask w, w, false)
    end
  | _ ->
    let x = to_z a and n = to_z b in
    let s = msb_z x w in
    if (not (Z.fits_int n)) || Z.to_int n >= w then (if s then ones w else zero w)
    else begin
      let k = Z.to_int n in
      let r = Z.shift_right x k in
      if s then mkz (Z.logor (Z.shift_left (zmax w) (w - k)) r) w else mkz r w
    end

(* BAP's order: width first, then the payload, with the two's-complement
   order when either side is signed. *)
let compare (a : t) (b : t) : int =
  let c = Stdlib.compare (bitwidth a) (bitwidth b) in
  if c <> 0 then c
  else begin
    let u =
      match a, b with
      | Small (x, _, _), Small (y, _, _) -> Stdlib.compare x y
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



let hash (t : t) : int =
  bitwidth t * 65599 lxor (if is_signed t then 1 else 0) lxor Z.hash (to_z t)

let min (a : t) (b : t) : t = if compare a b < 0 then a else b
let max (a : t) (b : t) : t = if compare a b > 0 then a else b

let extract_exn ?hi ?(lo = 0) (t : t) : t =
  let w = bitwidth t in
  let hi = match hi with Some h -> h | None -> w - 1 in
  let len = hi - lo + 1 in
  if len <= 0 then failwith "Cbat_word.extract: negative length";
  (* BAP sign-extends a signed source, and the extension vanishes when the
     result is reduced to [len] bits, so both arms are the plain slice. *)
  match t with
  | Small (v, _, _) -> Small ((if lo >= 62 then 0 else v lsr lo) land mask len, len, false)
  | Big (z, _, _) -> mkz (Z.extract z lo len) len

(* BIL cast to [sz] bits: HIGH reads the top bits, SIGNED sign-extends. *)
let cast (ct : Bil.cast) (sz : int) (t : t) : t =
  let w = bitwidth t in
  match ct with
  | Bil.UNSIGNED | Bil.LOW -> extract_exn ~hi:(sz - 1) t
  | Bil.SIGNED -> signed (extract_exn ~hi:(sz - 1) t)
  | Bil.HIGH -> extract_exn ~lo:(w - sz) t

let concat (a : t) (b : t) : t =
  let w = bitwidth a + bitwidth b in
  match a, b with
  | Small (x, _, _), Small (y, _, _) when w <= 62 ->
    Small (x lsl bitwidth b lor y land mask w, w, false)
  | _ -> mkz (Z.logor (Z.shift_left (to_z a) (bitwidth b)) (to_z b)) w

let rec gcd_int (a : int) (b : int) : int = if b = 0 then a else gcd_int b (a mod b)

let gcd_exn (a : t) (b : t) : t =
  let w = bitwidth a in
  match a, b with
  | Small (x, _, _), Small (y, _, _) ->
    if x = 0 then Small (y, w, false)
    else if y = 0 then Small (x, w, false)
    else Small (gcd_int x y land mask w, w, false)
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
  let z = to_z t in
  if Z.leq z (Z.of_int max_int) then Z.to_int z
  else if Z.leq z (Z.sub (Z.shift_left Z.one Sys.int_size) Z.one) then
    Z.to_int (Z.signed_extract z 0 Sys.int_size)
  else failwith (Printf.sprintf "%s doesn't fit the int type" (to_string t))

let to_int (t : t) : int Core_kernel.Or_error.t = Core_kernel.Or_error.try_with (fun () -> to_int_exn t)

let to_int64_exn (t : t) : int64 =
  let z = to_z t in
  if Z.leq z (Z.of_int64 Int64.max_int) then Z.to_int64 z
  else if Z.leq z (Z.sub (Z.shift_left Z.one 64) Z.one) then
    Z.to_int64 (Z.signed_extract z 0 64)
  else failwith (Printf.sprintf "%s doesn't fit the int64 type" (to_string t))

let to_int64 (t : t) : int64 Core_kernel.Or_error.t = Core_kernel.Or_error.try_with (fun () -> to_int64_exn t)

let pp (ppf : Format.formatter) (t : t) : unit = Format.fprintf ppf "%s" (to_string t)

let of_word (w : word) : t = of_string (Word.to_string w)
let to_word (t : t) : word = Word.of_string (to_string t)

let sexp_of_t (t : t) : Core_kernel.Sexp.t = Core_kernel.Sexp.Atom (to_string t)

let t_of_sexp (s : Core_kernel.Sexp.t) : t =
  match s with
  | Core_kernel.Sexp.Atom a -> of_string a
  | _ -> failwith "Cbat_word.t_of_sexp: expects an atom"

module Stringable = struct
  type nonrec t = t

  let to_string = to_string
  let of_string = of_string
end

include Core_kernel.Binable.Of_stringable_without_uuid (Stringable) [@@warning "-D"]

(* The [Cbat_word_ops] set, in terms of the ops above. *)

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

let cdiv (a : t) (b : t) : t =
  let d = div a b in
  if is_zero (modulo a b) then d else succ d

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
    let sx = signed ux and sy = signed uy in
    let q = div c d in
    let x0 = signed (mul_exact sx q) and y0 = signed (mul_exact sy q) in
    if not (is_zero (modulo c d)) then None
    else Some (extract_exn ~hi:(size - 1) x0, extract_exn ~hi:(size - 1) y0)
  end

let factor_2s (t : t) : t * int =
  let rec help (hi : int) (lo : int) : int =
    if hi = lo then hi
    else
      let mid = (hi + lo) / 2 in
      if is_zero (extract_exn ~hi:mid ~lo t) then help hi (mid + 1) else help mid lo
  in
  let w = bitwidth t in
  let lo = help (w - 1) 0 in
  (extract_exn ~hi:(w - 1 + lo) ~lo t, lo)

(* 2^i at [width] bits; shift amounts wrap mod 2^width like Word.lshift. *)
let dom_size ?width (i : int) : t =
  let wd = match width with Some x -> x | None -> i + 1 in
  if i < 0 then zero wd
  else
    let i' = i land ((1 lsl (Stdlib.min wd 62)) - 1) in
    if i' = 0 then one wd
    else if i' <= 61 then Small (1 lsl i', wd, false)
    else mkz (Z.shift_left Z.one i') wd

(* 2^(width-1) at [width] bits. *)
let half (w : int) : t = dom_size ~width:w (w - 1)

let cap_at_width ~width (t : t) : t =
  let w = bitwidth t in
  if w = width then t
  else if w < width then extract_exn ~hi:(width - 1) t
  else extract_exn ~hi:(width - 1) (min (pred (dom_size ~width:w width)) t)

(* Ordered infixes, defined last so the module's own uses of the
   Stdlib operators stay in scope. *)
let ( = ) (a : t) (b : t) : bool = compare a b = 0
let ( <> ) (a : t) (b : t) : bool = compare a b <> 0
let ( < ) (a : t) (b : t) : bool = compare a b < 0
let ( > ) (a : t) (b : t) : bool = compare a b > 0
let ( <= ) (a : t) (b : t) : bool = compare a b <= 0
let ( >= ) (a : t) (b : t) : bool = compare a b >= 0
