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

(* * Operations that can be performed on (binary) words. *)

open Bap.Std

val add_exact : word -> word -> word
val mul_exact : word -> word -> word
val succ_exact : word -> word
val lshift_exact : word -> int -> word


val cdiv : word -> word -> word

val gt_int : word -> int -> bool
val lt_int : word -> int -> bool

val is_one : word -> bool

val bounded_gcd : word -> word -> word

val bounded_diophantine : word -> word -> word -> (word * word) option

val factor_2s : word -> word * int

val count_initial_1s : word -> int

val lead_1_bit : word -> int option

val min : word -> word -> word
val max : word -> word -> word

(* * Computes the domain size, i.e., the number of elements that can be represented with a CLP of words that are all [i]-bits wide. *)
val dom_size : ?width : int -> int -> word

(* [half width]: 2^(width-1) at [width] bits — the first word of the high (negative-signed) half of the domain, the sign-bit threshold used by the signed-comparison rows and the sign-extension masks. *)
val half : int -> word

val cap_at_width : width:int -> word -> word

val add_bit : word -> word

val endian_string : Word.endian -> string
