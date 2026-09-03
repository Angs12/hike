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

(* Finite word sets. *)

type t [@@deriving bin_io, sexp]

include Cbat_wordset_intf.S with type t := t

val intersect_generic : (module Cbat_wordset_intf.S with type t = 'ws) ->  t -> 'ws -> t

val overlap_generic : (module Cbat_wordset_intf.S with type t = 'ws) ->  t -> 'ws -> bool
