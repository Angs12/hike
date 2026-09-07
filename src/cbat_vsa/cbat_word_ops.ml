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

include Bap.Std
module W = Cbat_word
module Option = Core_kernel.Option
open Cbat_vsa_utils

(* Multiply at the summed width; cannot overflow. *)
let mul_exact (w1 : W.t) (w2 : W.t) : W.t =
  let sz1 = W.bitwidth w1 in
  let sz2 = W.bitwidth w2 in
  let sz_ext = sz1 + sz2 in
  let w1_ext = W.extract_exn ~hi:(sz_ext - 1) w1 in
  let w2_ext = W.extract_exn ~hi:(sz_ext - 1) w2 in
  W.mul w1_ext w2_ext

let add_exact (w1 : W.t) (w2 : W.t) : W.t =
  let sz1 = W.bitwidth w1 in
  let sz2 = W.bitwidth w2 in
  let sz_ext = 1 + max sz1 sz2 in
  let w1_ext = W.extract_exn ~hi:(sz_ext - 1) w1 in
  let w2_ext = W.extract_exn ~hi:(sz_ext - 1) w2 in
  W.add w1_ext w2_ext

let succ_exact (w : W.t) : W.t =
  let width = W.bitwidth w in
  W.succ @@ W.extract_exn ~hi:width w

let lshift_exact (w : W.t) (i : int) : W.t =
  let width = i + W.bitwidth w in
  let wi = W.of_int ~width i in
  let w' = W.extract_exn ~hi:(width - 1) w in
  W.lshift w' wi

(* Bounded gcd. *)
let bounded_gcd (w1 : W.t) (w2 : W.t) : W.t =
  let width = W.bitwidth w1 in
  assert (width = W.bitwidth w2);
  if W.is_zero w1 then w2
  else if W.is_zero w2 then w1
  else W.gcd_exn w1 w2

(* Unsigned division rounding up. *)
let cdiv a b : W.t = if W.is_zero (W.modulo a b)
    then W.div a b else W.succ (W.div a b)

let is_one (w : W.t) : bool = W.is_zero (W.pred w)

(* Least non-negative x solving ax + by = c. *)
let bounded_diophantine (a : W.t) b c : (W.t * W.t) option =
  let size = W.bitwidth a in
  assert (size = W.bitwidth b);
  assert (size = W.bitwidth c);
  let zero = W.zero size in
  if W.is_zero c then Some (zero, zero)
  else if W.is_zero a && W.is_zero b then None
  else if W.is_zero a then
    if W.is_zero (W.modulo c b) then Some (zero, W.div c b) else None
  else if W.is_zero b then
    if W.is_zero (W.modulo c a) then Some (W.div c a, zero) else None
  else
    (* Bezout coefficients. *)
    let d, unsigned_x, unsigned_y = W.gcdext_exn a b in
    let signed_x = W.signed unsigned_x in
    let signed_y = W.signed unsigned_y in
    let gcd_quotient = W.div c d in
    (* Double-width products. *)
    let signed_x0 = W.signed (mul_exact signed_x gcd_quotient) in
    let signed_y0 = W.signed (mul_exact signed_y gcd_quotient) in
    if not (W.is_zero (W.modulo c d)) then None
    else
      (* Minimal-|x|,|y| solution pair. *)
      Some (W.extract_exn ~hi:(size-1) signed_x0,
            W.extract_exn ~hi:(size-1) signed_y0)

(* Split w into odd part and power of two. *)
let factor_2s (w : W.t) : W.t * int =
  let rec factor_help (hi : int) (lo : int) : int =
    if hi = lo then hi else
      let mid = (hi + lo) / 2 in
      let lo_part = W.extract_exn ~hi:mid ~lo w in
      if W.is_zero lo_part then factor_help hi (mid + 1)
      else factor_help mid lo
  in
  let width = W.bitwidth w in
  let lo = factor_help (width - 1) 0 in
  (* Keep the input width. *)
  let hi = width - 1 + lo in
  W.extract_exn ~hi ~lo w, lo


(* Position of the leading 1-bit. *)
let lead_1_bit (w : W.t) : int option =
  let rec lead_help (hi : int) (lo : int) : int option =
    let open Monads.Std.Monad.Option.Syntax in
    Option.some_if (hi >= lo) () >>= fun _ ->
    if hi = lo then !!hi else
    let mid = (hi + lo) / 2 in
    let hi_part = W.extract_exn ~hi ~lo:(mid + 1) w in
    if W.is_zero hi_part then lead_help mid lo
    else lead_help hi (mid + 1)
  in
  if W.is_zero w then None else lead_help ((W.bitwidth w) - 1) 0

let count_initial_1s (w : W.t) : int = snd @@ factor_2s @@ W.lnot w

let min w1 w2 : W.t = if W.compare w1 w2 < 0 then w1 else w2
let max w1 w2 : W.t = if W.compare w1 w2 < 0 then w2 else w1

(* 2^i at [width] bits. *)
(* Cached; hot on every CLP op. *)
let dom_size_cache : (int * int, W.t) Hashtbl.t = Hashtbl.create 16
let dom_size ?width (i : int) : W.t =
  let width = Option.value ~default:(i + 1) width in
  match Hashtbl.find_opt dom_size_cache (i, width) with
  | Some w -> w
  | None ->
    let w = W.lshift (W.one width) (W.of_int ~width i) in
    Hashtbl.add dom_size_cache (i, width) w;
    w

(* 2^(width-1) at [width] bits. *)
let half_cache : (int, W.t) Hashtbl.t = Hashtbl.create 8
let half (width : int) : W.t =
  match Hashtbl.find_opt half_cache width with
  | Some w -> w
  | None ->
    let one = W.one width in
    let i_wd = W.of_int ~width (width - 1) in
    let w = W.lshift one i_wd in
    Hashtbl.add half_cache width w;
    w

(* Closest value representable at [width] bits. *)
let cap_at_width ~width (w : W.t) : W.t =
  let w_width = W.bitwidth w in
  (* Exact width is the identity. *)
  if w_width = width then w
  else if w_width <= width then W.extract_exn ~hi:(width - 1) w else
    (* Largest width-bit number. *)
    let max_w = W.pred @@ dom_size ~width:w_width width in
    let res_val = min max_w w in
    W.extract_exn ~hi:(width - 1) res_val

(* Extend by one high bit. *)
let add_bit (w : W.t) : W.t =
  W.extract_exn ~hi:(W.bitwidth w) w

let endian_string : Word.endian -> string = function
  | BigEndian -> "BE"
  | LittleEndian -> "le"

let gt_int (w : W.t) (i : int) : bool =
  W.compare w (W.of_int ~width:(W.bitwidth w) i) > 0

let lt_int (w : W.t) (i : int) : bool =
  W.compare w (W.of_int ~width:(W.bitwidth w) i) < 0
