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

(* Word operations. *)

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

(* Number of values representable at [i] bits. *)
val dom_size : ?width : int -> int -> word

(* 2^(width-1) at [width] bits. *)
val half : int -> word

val cap_at_width : width:int -> word -> word

val add_bit : word -> word

val endian_string : Word.endian -> string
