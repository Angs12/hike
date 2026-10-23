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

  (* One key per address piece, every leaf of a mixed value fanned out. *)
  val of_wordset : WordSet.t -> t list

  (* The cell's stride: > 1 for a bounded strided address progression,
     1 for a plain hull. *)
  val step : t -> int

  (* The key's own line; cells of other lines never match a query. *)
  val origin : t -> Hike_origin.t option

  (* The key's hull ends as unsigned words, low end first. *)
  val hull : t -> Cbat_word.t * Cbat_word.t

  (* Same-grid strides keep their step; any mix demotes to 1. *)
  val combined_step : t -> t -> int

  (* Sub-ranges of [k] covered by no cell of [s]. *)
  val gaps : 'a -> t -> (t * 'a) seq -> (t * 'a) seq

  (* The key the landmark table records this cell under. *)
  val cell_key : t -> Cbat_landmarks.cell_desc

  (* Key ranges share at least one address. *)
  val overlap : t -> t -> bool

  (* The touched byte hull of a read anchored at [k]: the address hull
     grown by the access size. *)
  val expand : t -> bytes:int -> t

  val compare : t -> t -> int
end



module Val : sig

  type t

  module Idx : Cbat_lattice_intf.S_semi with type t = WordSet.idx * endian

  include Cbat_lattice_intf.S_indexed with type t := t and type idx = Idx.t

  val create : WordSet.t -> endian -> t

  val data : t -> WordSet.t

  val is_top : t -> bool
  val is_bottom : t -> bool

  val meet_poly : t -> t -> t

end



type t
type idx = {addr_width:int; addressable_width:int}

(* The index of [t]'s width facts. *)
val get_idx : t -> idx

include Value.S with type t := t

include Cbat_map_lattice.S_indexed with module Val := Val and module Key := Key and
type t := t and type idx := idx

(* A store of [data] at [key]: [strong] when [key] is the access's only
   address (a point key then overwrites); a weak store joins only the
   cells on its own grid at its width.  Every other cell whose bytes the
   store may write is dropped. *)
val store : t -> strong:bool -> key:Key.t -> data:Val.t -> t

(* Meet [data] into every cell whose key intersects [key]. *)
(* Meet into intersecting cells; an empty piece meet keeps the cell
   (never the dead-path bottom). *)
val meet_range_keep : t -> key:Key.t -> data:Val.t -> t

(* [widen_join] with the caller's per-key combiner: where the trees
   are comparable, each cell of the new tree combines with the old
   tree's value at the same key; join otherwise. *)
val widen_join_op : (Key.t -> Val.t -> Val.t -> Val.t) -> t -> t -> t

(* What a call leaves of the cells that name no stack line: [Drop_all]
   drops them all; [Keep_if f] keeps those whose key origin [f] accepts. *)
type foreign_cells = Drop_all | Keep_if of (Hike_origin.t option -> bool)

(* Keep stack cells at key >= [keep_lo] outside [stack_args], unless
   [clear_frame] removes every retained frame cell; [clear_from] removes
   those whose range reaches key >= it.  A cell is dropped whenever its
   key range overlaps an outgoing stack-argument range.  Cells that name
   no stack line follow [foreign_cells]. *)
val call_keep :
  t ->
  keep_lo:Cbat_word.t ->
  stack_args:(Cbat_word.t * Cbat_word.t) list ->
  clear_frame:bool ->
  clear_from:Cbat_word.t option ->
  foreign_cells:foreign_cells -> t

(* The values of the stack cells overlapping an outgoing stack-argument
   range (none when a bound is unkeyable). *)
val stack_arg_vals :
  t -> stack_args:(Cbat_word.t * Cbat_word.t) list -> Val.t list

(* Whether the map is the bottom map (no tree, no reads). *)
val is_bottom : t -> bool

(* Whether a stored cell's key intersects the byte range [lo, hi]
   (inclusive addresses); unkeyable bounds answer true. *)
val has_cell_in :
  t -> origin:Hike_origin.t option -> lo:Cbat_word.t -> hi:Cbat_word.t -> bool

(* The stored cells: key and value.  The treap walk is a full scan, so
   callers use it only where a per-cell decision is needed (the backward
   address filter's element-level coverage test), not per read. *)
val cells : t -> (Key.t * Val.t) list

