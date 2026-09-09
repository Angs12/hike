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

open !Core_kernel
open Bap.Std

module type S_semi = sig
  type t

  val top : t
  val join : t -> t -> t

  (* Join approximation that makes widening converge. *)
  val widen_join : t -> t -> t

  (* Partial order. *)
  val precedes : t -> t -> bool
  (* Equality; cheaper than [precedes]. *)
  val equal : t -> t -> bool

end


module type S = sig

  include S_semi

  val bottom : t
  val meet : t -> t -> t

end

(* Lattices indexed by another type; ops need equal indices. *)
module type S_indexed = sig
  type t
  type idx

  val get_idx : t -> idx
  val top : idx -> t
  val bottom : idx -> t

  val meet : t -> t -> t
  val join : t -> t -> t

  val widen_join : t -> t -> t

  val precedes : t -> t -> bool
  val equal : t -> t -> bool

end

module type S_val = sig
  type t
  include S with type t := t
  include Value.S with type t := t
end

module type S_indexed_val = sig
  type t
  include S_indexed with type t := t
  include Value.S with type t := t
end

module Free_index_val (L : S_val) : S_indexed_val
  with type idx = unit and type t = L.t
= struct
  type t = L.t [@@deriving bin_io, compare, sexp]
  type idx = unit

  let get_idx _ = ()
  let top _ = L.top
  let bottom _ = L.bottom

  let meet = L.meet
  let join = L.join

  let widen_join = L.widen_join

  let precedes = L.precedes
  let equal = L.equal

  let sexp_of_t = L.sexp_of_t

  let pp = L.pp

end
