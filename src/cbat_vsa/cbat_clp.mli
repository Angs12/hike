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

open Bap.Std

(* Circular linear progressions. *)

type direction = Finite | Ascending | Descending | Circular
[@@deriving bin_io, sexp, compare]

type t [@@deriving bin_io, sexp]

include Cbat_wordset_intf.S with type t := t

val create : ?width:int -> ?step:word -> ?cardn: word -> word -> t
val create_ascending : width:int -> base:word -> step:word -> t
val create_descending : width:int -> base:word -> step:word -> t

(* Step-1 CLP [lo, hi]; a wrapped pair is the circular interval. *)
val interval : width:int -> word -> word -> t

val nearest_pred : word -> t -> word option
val nearest_succ : word -> t -> word option

(* Step-1 CLP from (base, step); circular when the progression wraps. *)
val infinite : word * word -> t

val is_top : t -> bool
val is_infinite : t -> bool
val is_bottom : t -> bool
val is_ascending : t -> bool
val is_descending : t -> bool
val is_circular : t -> bool

val subset : t -> t -> bool
val translate : t -> word -> t

val widen_join : t -> t -> t
val extrapolate_steps : steps:int -> t -> t -> t



