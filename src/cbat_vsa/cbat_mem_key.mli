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

open Core
open Bap.Std

type point = {pwidth : int; pvalue : int64} [@@deriving bin_io, sexp]

type t = {lo : point; hi : point; step : int} [@@deriving bin_io, sexp]

val compare : t -> t -> int
val compare_point : point -> point -> int
val equal : point -> point -> bool
val lt : point -> point -> bool
val le : point -> point -> bool
val gt : point -> point -> bool
val ge : point -> point -> bool
val min : point -> point -> point
val max : point -> point -> point
val is_zero : point -> bool
val succ : point -> point

val of_word : Cbat_word.t -> point option
val upper : t -> point
val lower : t -> point
val step : t -> int
val cell_key : t -> Cbat_landmarks.Cell_key.t
val combined_step : t -> t -> int
val covers : t -> t -> bool
val piece : t -> lo:point -> hi:point -> t
type 'a up_to_two = [`none | `one of 'a | `two of 'a * 'a]

val interval_diff : t -> t -> t up_to_two
val gaps : 'a -> t -> (t * 'a) seq -> (t * 'a) seq
val overlap : t -> t -> bool
val of_wordset : Cbat_clp_set_composite.t -> t option
val union : t -> t -> t
val intersection : t -> t -> t
val read_aligned : bits:int -> step:int -> point -> point -> bool

type side = Left | Right | Both_sides
val seq_product : t seq -> t seq -> (side * t) seq

val pp : Format.formatter -> t -> unit
val sexp_of_t : t -> Sexp.t
val t_of_sexp : Sexp.t -> t
