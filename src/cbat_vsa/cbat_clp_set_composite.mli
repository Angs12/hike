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

(* The runtime origin of a relative value. *)
module Origin = Hike_origin

(* The value's runtime origin: [Some o] exactly when every piece of the
   value is relative to the one origin [o]; absolute, plain, and
   mixed-origin values are [None]. *)
val origin : t -> Origin.t option

(* Re-tags a relative value's origin, offsets unchanged — the VLA
   seed's framing step (the entry-line positions ARE the new frame's). *)
val set_origin : Origin.t -> t -> t

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

(* The symbolic stack base: base + exact offsets; shape-losing ops
   degrade to the plain hull; bit-ops compute within the certified low
   nibble (the ABI entry residue 8 (mod 16)) and answer top beyond
   it. *)

(* The segment base (2^62 + 8: the ABI entry residue — a call-entered
   RSP is 8 (mod 16)), as int64. *)
val stack_base : int64

val stack_word : Cbat_clp.t -> t
val stack_word_i64 : int64 -> t

(* A fresh VLA frame named by the SP-assigning def: offset 0 is the
   allocation base (the post-move SP). *)
val vla_frame : Bap.Std.Tid.t -> t

(* The offset set of a stack-symbolic value — [Some offs] ONLY for the
   symbolic arm; a plain in-band set is None.  A VLA value's offsets are
   materialised onto the entry line through its base range; an unknown
   base answers None. *)
val stack_offsets : t -> Cbat_clp.t option

(* The frame-relative offsets of a VLA value (0 = the allocation base) —
   [Some] only for the [Vla] origin. *)
val vla_offsets : t -> Cbat_clp.t option

(* Memory keys retain the carried origin's line; plain values stay absolute. *)
val address_pieces : t -> (Origin.t * Cbat_clp.Pieces.t) option

(* Memory namespaces: Stack, Window and Vla share the stack line;
   Rip and Abs each retain their own line. *)
val key_line : Origin.t -> Origin.t

(* The set's own address stride: > 1 only for a bounded strided Clp or
   stack-offset progression; 1 otherwise. *)
val stride : t -> int

(* Stack identity requires a Stack, Window or Vla runtime origin. *)
val in_stack_segment : t -> bool

(* The offset set's extrema of a stack-symbolic value; None for a
   plain value. *)
val offset_extrema : t -> (Cbat_word.t * Cbat_word.t) option

(* The singleton word of a plain operand, if it is one. *)
val singleton_of : t -> Cbat_word.t option

(* The solve-boundary refinement: a wholly window-side relative value
   (every offset at/above the ABI word) names the caller's frame
   origin. *)
val refine_origin : word:int -> t -> t

(* Segment-relative bounds of a stack value; None when not stack. *)
val stack_bounds : t -> (int64 * int64) option

(* A non-bottom set's classification on the model's absolute
   segment line; a bottom set has no values to classify. *)
type kind =
  | Range of int64 * int64
  | Infinite of int64 * int64
  | Caller of int64 * int64
  | Mixed of int64 * int64

val equal_kind : kind -> kind -> bool

val unbounded_span : kind
val is_unbounded_span : int64 -> int64 -> bool
val position_of_offset : int64 -> int64 option

(* The per-progression [min, max] positions of a stack-symbolic value's
   offsets — the disjoint runs the attribution clips per run. *)
val offset_runs : t -> (int64 * int64) list
val caller_split : kind -> kind
val classify : t -> kind

(* The elements when the set is enumerable within [cap]; [None] = the
   count exceeds the budget. *)
val enumerate : cap:int -> t -> Cbat_word.t list option

#ifdef VSA_DEBUG
(* The value's constructor, for the churn diagnosis. *)
val tag : t -> string
#endif
