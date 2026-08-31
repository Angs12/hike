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

open Core_kernel
open Bap.Std

(* * Cbat_ai_memmap Represents memory as an interval tree from ranges of addresses to CLPs with an endianness. *)

module WordSet = Cbat_clp_set_composite

module Key : sig

  type t

  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

  val of_wordset : WordSet.t -> t option
end



module Val : sig

  type t

  module Idx : Cbat_lattice_intf.S_semi with type t = WordSet.idx * endian

  include Cbat_lattice_intf.S_indexed with type t := t and type idx = Idx.t

  val create : WordSet.t -> endian -> t

  val data : t -> WordSet.t

  val is_top : t -> bool
  val is_bottom : t -> bool

  val join_at : idx -> t -> t -> t
  val meet_at : idx -> t -> t -> t


  val join_poly : t -> t -> t
  val meet_poly : t -> t -> t

end



type t
type idx = {addr_width:int; addressable_width:int}

include Value.S with type t := t

include Cbat_map_lattice.S_indexed with module Val := Val and module Key := Key and
type t := t and type idx := idx

(* Hike addition (the trace-partitioning design, docs/trace-partitioning-plan.md §3): the RANGED meet — meet [data] into every cell whose key intersects [key]: the overlapping cells meet [data], the gaps within [key]. *)
val meet_range : t -> key:Key.t -> data:Val.t -> t

(* Hike addition (the call-abstraction precision lane): the caller-frame-preserving call abstraction — keep every cell whose key is >= [keep_lo] (the caller's own locals; the callee's frame is below the call-time RSP) and. *)
val call_keep : t -> keep_lo:Bap.Std.word -> escape:(Bap.Std.word * Bap.Std.word) list -> t

