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

(* Circular linear progressions.  A Finite progression never crosses
   2^width: one that would is its two arcs.  The set operations live in
   [Pieces]. *)

type direction = Finite | Ascending | Descending | Circular
[@@deriving bin_io, sexp, compare]

(* The core's record, so the arithmetic rules of [Cbat_clp_arith] apply
   to it. *)
type t = Cbat_clp_core.t [@@deriving bin_io, sexp, compare]

type word = Cbat_word.t

(* The progression {base + n*step | n < cardn}; a Finite one must not
   cross 2^width (use [arcs] when it may). *)
val create : ?width:int -> ?step:Cbat_word.t -> ?cardn: Cbat_word.t -> Cbat_word.t -> t

(* The same progression as its non-bottom, non-crossing pieces, ascending:
   one, or the low and the high arc across the modulus. *)
val arcs : ?width:int -> ?step:Cbat_word.t -> ?cardn: Cbat_word.t -> Cbat_word.t -> t list

val create_ascending : width:int -> base:Cbat_word.t -> step:Cbat_word.t -> t
val create_descending : width:int -> base:Cbat_word.t -> step:Cbat_word.t -> t

val singleton : word -> t
val bottom : int -> t
val top : int -> t

(* Unbounded progression at (base, step). *)
val infinite : Cbat_word.t * Cbat_word.t -> t

val bitwidth : t -> int
val cardinality : t -> word
val min_elem : t -> word option
val max_elem : t -> word option
val min_elem_signed : t -> word option
val max_elem_signed : t -> word option

(* The progression's step (0 for singletons). *)
val step_of : t -> Cbat_word.t

(* True when elements are spaced by a multiple of [w]. *)
val splits_by : t -> word -> bool

val elem : word -> t -> bool
val iter : t -> word list
val equal : t -> t -> bool
val overlap : t -> t -> bool
val pp : Format.formatter -> t -> unit

val nearest_pred : Cbat_word.t -> t -> Cbat_word.t option
val nearest_succ : Cbat_word.t -> t -> Cbat_word.t option

val is_top : t -> bool
val is_infinite : t -> bool
val is_bottom : t -> bool
val is_ascending : t -> bool
val is_descending : t -> bool
val is_circular : t -> bool

(* The elements at most [n], and the rest. *)
val split_at_n : t -> Cbat_word.t -> t * t

val subset : t -> t -> bool
val intersection : t -> t -> t

(* The widening of an iterate by its successor, as pieces. *)
val widen_join : t -> t -> t list
val extrapolate_steps : steps:int -> t -> t -> t list

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
  (* A result's pieces: one progression or the two arcs of one across the
     modulus, ascending. *)
  val of_arcs : progression list -> t
  (* Merge ascending progression streams, without combining or capping. *)
  val merge_progressions : progression list -> progression list -> progression list
  (* Build from disjoint, ascending, non-bottom progressions. *)
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

  (* The smallest arc of the circle holding every piece: one piece, or the
     two arcs of one across the modulus. *)
  val circular_hull : t -> t
  val hull_union : t -> t -> t
  (* [p] met with a hull, as a hull. *)
  val hull_intersection : progression -> t -> t
  (* The step of the progression a hull denotes. *)
  val hull_step : t -> Cbat_word.t
  val hull_add : t -> t -> t
  val hull_sub : t -> t -> t
  (* The hull of an ascending, deduplicated word list. *)
  val hull_of_list : width:int -> Cbat_word.t list -> t
  (* [widen_hulls f a b]: [f] on single-piece hulls; a hull across the
     modulus widens to its circular grid. *)
  val widen_hulls :
    (progression -> progression -> progression list) -> t -> t -> t
  val pp : Format.formatter -> t -> unit
end

(* The step-1 interval [lo, hi] as pieces; a pair with [hi < lo] is the
   circular interval across the modulus. *)
val interval : width:int -> Cbat_word.t -> Cbat_word.t -> Pieces.t

(* The exact finite element set as an uncapped flat ascending array of
   words (ADR 0036).  No budget — the caller's
   canonical promotion applies the budget.  [to_pieces] is the run view. *)
module Exact : sig
  type t [@@deriving bin_io, sexp, compare]

  val to_pieces : t -> progression list

  val bottom : int -> t
  val singleton : Cbat_word.t -> t
  val of_list : width:int -> Cbat_word.t list -> t
  (* Compute an arbitrary image into an ordered, distinct set during production. *)
  val of_iter : width:int -> iter:((Cbat_word.t -> unit) -> unit) -> t
  (* Strictly ascending, distinct, unsigned words at [width]. *)
  val of_sorted_list : width:int -> Cbat_word.t list -> t
  (* The elements [f] accepts, [f] called once per element in ascending
     order; the set itself when every element survives. *)
  val filter : t -> f:(Cbat_word.t -> bool) -> t
  val is_bottom : t -> bool
  (* The same elements as a canonical piece union. *)
  val pieces : t -> Pieces.t
  (* The elements of a piece union at their common [width]. *)
  val of_pieces : width:int -> Pieces.t -> t

  val bitwidth : t -> int
  val count : t -> int
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
  val overlap_elem : width:int -> elem:(Cbat_word.t -> bool) -> t -> bool

  val get_idx : t -> int
  val pp : Format.formatter -> t -> unit
end



