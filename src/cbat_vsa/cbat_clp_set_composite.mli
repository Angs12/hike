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

(* The certified width: the low bits of the base that are a fact (the
   entry residue's nibble). *)
val certified_bits : int

(* The plain-arm band's lower bound; the band is
   [stack_band_lo, 2^63) — unreachable for real addresses. *)
val stack_band_lo : int64

(* The VLA band: a runtime-sized allocation relocates its SP to
   [stack_base + vla_anchor] minus the size, so its claims live in
   [vla_floor, vla_anchor) — disjoint from the frame line by
   construction.  [vla_span] caps the rebased sizes. *)
val vla_anchor : int64
val vla_span : int64
val vla_floor : int64

val stack_word : Cbat_clp.t -> t
val stack_word_i64 : int64 -> t

(* The offset set of a stack-symbolic value — [Some offs] ONLY for the
   symbolic arm; a plain in-band set is None. *)
val stack_offsets : t -> Cbat_clp.t option

(* The address pieces a memory key fans over: the symbolic offsets'
   piece union, a plain in-band value's segment-relative translation,
   or a plain out-of-band value's own pieces.  None when the value
   names no bounded address line. *)
val address_pieces : t -> Cbat_clp.Pieces.t option

(* The set's own address stride: > 1 only for a bounded strided Clp or
   stack-offset progression; 1 otherwise. *)
val stride : t -> int

(* Stack residency: the symbolic arm, or a bounded plain hull inside
   the signed-positive band [2^61, 2^63) — unreachable for real
   addresses. *)
val in_stack_segment : t -> bool

(* The offset set's extrema of a stack-symbolic value; None for a
   plain value. *)
val offset_extrema : t -> (Cbat_word.t * Cbat_word.t) option

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

(* The per-progression [min, max] positions of a stack-symbolic value's
   offsets — the disjoint runs the attribution clips per run. *)
val offset_runs : t -> (int64 * int64) list
val caller_split : kind -> kind
val classify : t -> kind

(* The elements when the set is enumerable within [cap]; [None] = the
   count exceeds the budget. *)
val enumerate : cap:int -> t -> Cbat_word.t list option
