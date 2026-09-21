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

type t

(* The CLP domain this set is built over. *)
module Clp = Cbat_clp

include Cbat_wordset_intf.S with type t := t

val is_top : t -> bool
val is_bottom : t -> bool
val is_infinite : t -> bool
val is_ascending : t -> bool
val is_descending : t -> bool
val is_circular : t -> bool

val of_clp : Cbat_clp.t -> t

val widen_join : t -> t -> t
val extrapolate_steps : steps:int -> t -> t -> t

(* The symbolic stack base.  [StackOff offs] = the model stack
   segment base (non-canonical, disjoint from every real x86-64
   address) plus the exact offset set; shape-losing ops degrade to the
   plain exact hull, and ops that keep unknown bits of the base answer
   top — the base is a tag except for its ABI-certified low nibble
   (the entry residue 8 (mod 16)), within which bit-ops compute. *)

(* The segment base (2^62), as int64. *)
val stack_base : int64

val stack_word : Cbat_clp.t -> t
val stack_word_i64 : int64 -> t

(* The offset set of a stack-symbolic value — [Some offs] ONLY for the
   symbolic arm; a plain in-band set is None. *)
val stack_offsets : t -> Cbat_clp.t option

(* Stack residency: the symbolic arm, or a bounded plain hull inside
   the signed-positive band [2^61, 2^63) — unreachable for real
   addresses. *)
val in_stack_segment : t -> bool

(* The offset set's extrema of a stack-symbolic value; None for a
   plain value. *)
val offset_extrema : t -> (Cbat_word.t * Cbat_word.t) option

(* The offset set's extrema of a stack-symbolic value; None for a
   plain value. *)

(* Segment-relative bounds of a stack value; None when not stack. *)
val stack_bounds : t -> (int64 * int64) option

(* The def-carried classification of a set on the model's absolute
   segment line. *)
type kind =
  | Range of int64 * int64
  | Infinite of int64 * int64
  | Caller of int64 * int64
  | Mixed of int64 * int64
  | Dead

val equal_kind : kind -> kind -> bool

val unbounded_span : kind
val is_unbounded_span : int64 -> int64 -> bool
val position_of_offset : int64 -> int64 option
val caller_split : kind -> kind
val classify : t -> kind

(* The elements when the set is enumerable within [cap]; [None] = the
   count exceeds the budget. *)
val enumerate : cap:int -> t -> Cbat_word.t list option
