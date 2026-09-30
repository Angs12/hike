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

type t = {origin : Hike_origin.t; lo : point; hi : point; step : int}
[@@deriving bin_io, sexp]

val origin : t -> Hike_origin.t
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
val cell_key : t -> Cbat_landmarks.cell_desc
val combined_step : t -> t -> int
val covers : t -> t -> bool
val piece : t -> lo:point -> hi:point -> t
val interval_diff : t -> t -> t list
val gaps : 'a -> t -> (t * 'a) seq -> (t * 'a) seq
val overlap : t -> t -> bool

(* The touched byte hull of a read anchored at [k]: the address hull
   grown by the access size. *)
val expand : t -> bytes:int -> t
(* One key per piece of the value's address line (capped at the piece
   union's cap); every fanned entry stores the full value. *)
val of_wordset : Cbat_clp_set_composite.t -> t list
val union : t -> t -> t
val intersection : t -> t -> t
val read_aligned : bits:int -> step:int -> point -> point -> bool

type side = Left | Right | Both_sides
val seq_product : t seq -> t seq -> (side * t) seq

val pp : Format.formatter -> t -> unit
val sexp_of_t : t -> Sexp.t
val t_of_sexp : Sexp.t -> t
