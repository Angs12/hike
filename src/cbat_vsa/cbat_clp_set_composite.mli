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

(* The symbolic stack base (T3).  [StackOff offs] = the model stack
   segment base (an unknown value in [stack_base, stack_base +
   stack_span] — non-canonical, disjoint from every real x86-64
   address) plus the exact offset set.  The base is a constant model
   fact: arithmetic with base-free operands propagates offsets
   exactly; shape-losing ops degrade to the plain concrete hull. *)

(* The segment base (2^62) and span (8 MiB), as int64. *)
val stack_base : int64
val stack_span : int64

(* The stack word over an offset set. *)
val stack_word : Cbat_clp.t -> t

(* The singleton-offset stack word. *)
val stack_word_i64 : int64 -> t

(* The offset set of a stack-symbolic value — the StackOff PROOF
   (T14): [Some offs] ONLY for the symbolic arm; a plain in-band set
   (the degraded band arm) is None.  This is the accessor for every
   "is this value FROM this sub's SP" question (frame extents, the
   escape decision); the band re-tag stays for ADDRESS
   classification via [in_stack_segment]. *)
val stack_offsets : t -> Cbat_clp.t option

(* Stack residency: the symbolic arm, or the plain degraded arm (a
   bounded plain hull inside the signed-positive band [2^61, 2^63) —
   unreachable for real addresses). *)
val in_stack_segment : t -> bool

(* Segment-relative bounds of a stack value; None when not stack. *)
val stack_bounds : t -> (int64 * int64) option

(* The offset-space twin (the tag universe); None when not stack. *)
val relativize : t -> t option
