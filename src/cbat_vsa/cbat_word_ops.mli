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

val add_exact : Cbat_word.t -> Cbat_word.t -> Cbat_word.t
val mul_exact : Cbat_word.t -> Cbat_word.t -> Cbat_word.t
val succ_exact : Cbat_word.t -> Cbat_word.t
val lshift_exact : Cbat_word.t -> int -> Cbat_word.t


val cdiv : Cbat_word.t -> Cbat_word.t -> Cbat_word.t

val gt_int : Cbat_word.t -> int -> bool

val is_one : Cbat_word.t -> bool

val bounded_gcd : Cbat_word.t -> Cbat_word.t -> Cbat_word.t

val bounded_diophantine : Cbat_word.t -> Cbat_word.t -> Cbat_word.t -> (Cbat_word.t * Cbat_word.t) option

val factor_2s : Cbat_word.t -> Cbat_word.t * int

val count_initial_1s : Cbat_word.t -> int

val lead_1_bit : Cbat_word.t -> int option

val min : Cbat_word.t -> Cbat_word.t -> Cbat_word.t
val max : Cbat_word.t -> Cbat_word.t -> Cbat_word.t

(* Number of values representable at [i] bits. *)
val dom_size : ?width : int -> int -> Cbat_word.t

(* 2^(width-1) at [width] bits. *)
val half : int -> Cbat_word.t

val cap_at_width : width:int -> Cbat_word.t -> Cbat_word.t

val add_bit : Cbat_word.t -> Cbat_word.t

val endian_string : Word.endian -> string
