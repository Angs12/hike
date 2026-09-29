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

(* Memory as an interval tree from address ranges to CLPs with endianness. *)

module WordSet = Cbat_clp_set_composite

module Key : sig

  type t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

  val of_wordset : WordSet.t -> t list

  (* The cell's stride: > 1 for a bounded strided address progression,
     1 for a plain hull. *)
  val step : t -> int

  (* Same-grid strides keep their step; any mix demotes to 1. *)
  val combined_step : t -> t -> int

  (* Sub-ranges of [k] covered by no cell of [s]. *)
  val gaps : 'a -> t -> (t * 'a) seq -> (t * 'a) seq

  (* The key the landmark table records this cell under. *)
  val cell_key : t -> Cbat_landmarks.Cell_key.t

  (* Key ranges share at least one address. *)
  val overlap : t -> t -> bool
end



module Val : sig

  type t

  module Idx : Cbat_lattice_intf.S_semi with type t = WordSet.idx * endian

  include Cbat_lattice_intf.S_indexed with type t := t and type idx = Idx.t

  val create : WordSet.t -> endian -> t

  val data : t -> WordSet.t

  val is_top : t -> bool
  val is_bottom : t -> bool

  val join_poly : t -> t -> t
  val meet_poly : t -> t -> t

end



type t
type idx = {addr_width:int; addressable_width:int}

(* The index of [t]'s width facts. *)
val get_idx : t -> idx

include Value.S with type t := t

include Cbat_map_lattice.S_indexed with module Val := Val and module Key := Key and
type t := t and type idx := idx

(* Meet [data] into every cell whose key intersects [key]. *)
val meet_range : t -> key:Key.t -> data:Val.t -> t

(* [widen_join] with the caller's per-key combiner: where the trees
   are comparable, each cell of the new tree combines with the old
   tree's value at the same key; join otherwise. *)
val widen_join_op : (Key.t -> Val.t -> Val.t -> Val.t) -> t -> t -> t

(* Keep cells at key >= [keep_lo] outside [escape]. *)
val call_keep :
  t ->
  keep_lo:Bap.Std.word ->
  escape:(Bap.Std.word * Bap.Std.word) list -> t

(* Whether the map is the bottom map (no tree, no reads). *)
val is_bottom : t -> bool

(* Whether a stored cell's key intersects the byte range [lo, hi]
   (inclusive addresses); unkeyable bounds answer true. *)
val has_cell_in :
  t -> origin:Hike_origin.t -> lo:Cbat_word.t -> hi:Cbat_word.t -> bool

#ifdef VSA_DEBUG
(* The stored cells, for the churn diagnosis. *)
val cells : t -> (Key.t * Val.t) list
#endif

