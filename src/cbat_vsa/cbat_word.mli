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

(* The domain's numeric substrate.

   [Small] holds an int63 immediate, [Big] a [Z.t]; the split is by VALUE
   MAGNITUDE, never by declared width.  Each op works in machine ints when
   both operands are [Small] and the result stays in the int63 range, and in
   [Z.t] otherwise; the [Z.t] arm is the same op at arbitrary precision, so
   a fall back is exact.

   A value is the canonical payload [0 <= v < 2^width], with the signed flag
   carried beside it.  Arithmetic results are unsigned. *)

open Bap.Std

type t = Small of int * int * bool | Big of Z.t * int * bool

val bitwidth : t -> int
val is_signed : t -> bool
val signed : t -> t
val unsigned : t -> t
val to_z : t -> Z.t
val of_z : Z.t -> int -> t

val zero : int -> t
val one : int -> t
val ones : int -> t
val b0 : t
val b1 : t
val of_int : width:int -> int -> t
val of_int64 : ?width:int -> int64 -> t

val is_zero : t -> bool
val is_one : t -> bool
val msb : t -> bool
val lsb : t -> bool

val succ : t -> t
val pred : t -> t
val neg : t -> t
val lnot : t -> t
val abs : t -> t
val add : t -> t -> t
val sub : t -> t -> t
val mul : t -> t -> t
val div : t -> t -> t
val modulo : t -> t -> t
val smodulo : t -> t -> t
val logand : t -> t -> t
val logor : t -> t -> t
val logxor : t -> t -> t
val lshift : t -> t -> t
val rshift : t -> t -> t
val arshift : t -> t -> t

val compare : t -> t -> int
val equal : t -> t -> bool
(* Ordered infixes; mirroring Bap.Std.Word's surface. *)
val ( = ) : t -> t -> bool
val ( <> ) : t -> t -> bool
val ( < ) : t -> t -> bool
val ( > ) : t -> t -> bool
val ( <= ) : t -> t -> bool
val ( >= ) : t -> t -> bool
val hash : t -> int
val min : t -> t -> t
val max : t -> t -> t

val extract_exn : ?hi:int -> ?lo:int -> t -> t
val cast : Bil.cast -> int -> t -> t
val concat : t -> t -> t

val gcd_exn : t -> t -> t
val lcm_exn : t -> t -> t
val gcdext_exn : t -> t -> t * t * t

val to_int_exn : t -> int
val to_int : t -> int Core_kernel.Or_error.t
val to_int64_exn : t -> int64
val to_int64 : t -> int64 Core_kernel.Or_error.t

val to_string : t -> string
val of_string : string -> t
val pp : Format.formatter -> t -> unit

(* BAP-facing edges. *)
val of_word : word -> t
val to_word : t -> word

val sexp_of_t : t -> Core_kernel.Sexp.t
val t_of_sexp : Core_kernel.Sexp.t -> t
include Core_kernel.Binable.S with type t := t

(* The [Cbat_word_ops] set. *)

val mul_exact : t -> t -> t
val add_exact : t -> t -> t
val succ_exact : t -> t
val lshift_exact : t -> int -> t

(* Both require equal-width operands. *)
val bounded_gcd : t -> t -> t
val bounded_diophantine : t -> t -> t -> (t * t) option

(* Unsigned division rounding up. *)
val cdiv : t -> t -> t

(* Splits into the odd part and the power of two. *)
val factor_2s : t -> t * int

val dom_size : ?width:int -> int -> t
val half : int -> t
val cap_at_width : width:int -> t -> t
