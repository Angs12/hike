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

include Cbat_wordset_intf.S with type t := t and type word = Cbat_word.t

val create : ?width:int -> ?step:Cbat_word.t -> ?cardn: Cbat_word.t -> Cbat_word.t -> t
val create_ascending : width:int -> base:Cbat_word.t -> step:Cbat_word.t -> t
val create_descending : width:int -> base:Cbat_word.t -> step:Cbat_word.t -> t

(* Step-1 CLP [lo, hi]; a wrapped pair is the circular interval. *)
val interval : width:int -> Cbat_word.t -> Cbat_word.t -> t

(* The progression's step (0 for singletons). *)
val step_of : t -> Cbat_word.t

val nearest_pred : Cbat_word.t -> t -> Cbat_word.t option
val nearest_succ : Cbat_word.t -> t -> Cbat_word.t option

(* Unbounded progression at (base, step). *)
val infinite : Cbat_word.t * Cbat_word.t -> t

val is_top : t -> bool
val is_infinite : t -> bool
val is_bottom : t -> bool
val is_ascending : t -> bool
val is_descending : t -> bool
val is_circular : t -> bool
val is_wrapped : t -> bool

(* A wrapped Finite piece's two non-wrapping arcs. *)
val split_wrapped : t -> t list

(* The elements at most [n], and the rest. *)
val split_at_n : t -> Cbat_word.t -> t * t

val subset : t -> t -> bool
val translate : t -> Cbat_word.t -> t

val widen_join : t -> t -> t
val extrapolate_steps : steps:int -> t -> t -> t

(* The progression type, named for the [Pieces] signature. *)
type progression = t [@@deriving bin_io, sexp, compare]

(* The canonical, capped union of progressions.  The smart constructors
   are the only way in; the type is abstract and the list is never
   exposed as a raw value. *)
module Pieces : sig
  type t [@@deriving bin_io, sexp, compare]

  val to_list : t -> progression list
  val fold : t -> init:'a -> f:('a -> progression -> 'a) -> 'a
  val iter : t -> f:(progression -> unit) -> unit
  val elements : t -> Cbat_word.t list

  val of_progression : progression -> t
  (* Merge ascending progression streams, without combining or capping. *)
  val merge_progressions : progression list -> progression list -> progression list
  (* Build from disjoint, ascending, non-wrapping, non-bottom progressions. *)
  val of_progressions : progression list -> t
  val of_list : width:int -> Cbat_word.t list -> t
  val singleton : Cbat_word.t -> t
  val top : int -> t
  val bottom : int -> t

  val bitwidth : t -> int
  val is_top : t -> bool
  val is_bottom : t -> bool
  val min_elem : t -> Cbat_word.t option
  val max_elem : t -> Cbat_word.t option
  val min_elem_signed : t -> Cbat_word.t option
  val max_elem_signed : t -> Cbat_word.t option
  val cardinality : t -> Cbat_word.t
  (* [gt_int (cardinality t) n], without building the sum. *)
  val card_exceeds : int -> t -> bool
  val elem : Cbat_word.t -> t -> bool
  val equal : t -> t -> bool
  val precedes : t -> t -> bool
  val overlap : t -> t -> bool
  val splits_by : t -> Cbat_word.t -> bool
  val is_ascending : t -> bool
  val is_descending : t -> bool
  val is_circular : t -> bool

  val union : t -> t -> t
  val intersection : t -> t -> t
  val diff : t -> t -> t
  val join : t -> t -> t
  val meet : t -> t -> t
  val widen_join : t -> t -> t
  val extrapolate_steps : steps:int -> t -> t -> t
  val translate : t -> Cbat_word.t -> t

  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val sdiv : t -> t -> t
  val modulo : t -> t -> t
  val smodulo : t -> t -> t
  val arshift : t -> t -> t
  val rshift : t -> t -> t
  val lshift : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val lnot : t -> t
  val neg : t -> t
  val extract : ?hi:int -> ?lo:int -> t -> t
  val cast : Bil.cast -> int -> t -> t
  val concat : t -> t -> t
end

(* The exact finite element set as an uncapped flat ascending array of
   words (ADR 0036).  No budget — the caller's
   canonical promotion applies the budget.  [to_pieces] is the run view. *)
module Exact : sig
  type t [@@deriving bin_io, sexp, compare]

  val to_pieces : t -> progression list

  val bottom : int -> t
  val singleton : Cbat_word.t -> t
  val of_list : width:int -> Cbat_word.t list -> t
  (* Strictly ascending, distinct, unsigned words at [width]. *)
  val of_sorted_list : width:int -> Cbat_word.t list -> t
  val is_bottom : t -> bool
  (* A one-element set's pieces: [create] makes every singleton
     canonical, so they are the ones [Pieces.of_list] would build. *)
  val point_pieces : t -> Pieces.t option
  (* The same elements as a canonical piece union. *)
  val pieces : t -> Pieces.t
  (* The elements of a piece union at their common [width]. *)
  val of_pieces : width:int -> Pieces.t -> t

  val bitwidth : t -> int
  val cardinality : t -> Cbat_word.t
  (* [gt_int (cardinality t) n], without building the sum. *)
  val card_exceeds : int -> t -> bool
  val elem : Cbat_word.t -> t -> bool
  val iter : t -> Cbat_word.t list
  val elements : t -> Cbat_word.t list

  val equal : t -> t -> bool
  val overlap : t -> t -> bool

  val union : t -> t -> t
  val intersection : t -> t -> t
  val diff : t -> t -> t
  val join : t -> t -> t
  val meet : t -> t -> t
  val widen_join : t -> t -> t

  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val sdiv : t -> t -> t
  val modulo : t -> t -> t
  val smodulo : t -> t -> t
  val arshift : t -> t -> t
  val rshift : t -> t -> t
  val lshift : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t

  val lnot : t -> t
  val neg : t -> t
  val extract : ?hi:int -> ?lo:int -> t -> t
  val cast : Bil.cast -> int -> t -> t
  val concat : t -> t -> t

  val splits_by : t -> Cbat_word.t -> bool
  val precedes : t -> t -> bool
  val min_elem : t -> Cbat_word.t option
  val max_elem : t -> Cbat_word.t option
  val min_elem_signed : t -> Cbat_word.t option
  val max_elem_signed : t -> Cbat_word.t option
  val overlap_generic :
    (module Cbat_wordset_intf.S with type t = 'ws) -> t -> 'ws -> bool

  val get_idx : t -> int
  val pp : Format.formatter -> t -> unit
end



