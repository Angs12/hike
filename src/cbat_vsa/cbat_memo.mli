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

(* The VERSION-KEYED MEMO interface (architecture review #2).  The
   change-driven-cache discipline — stamp / validity / stale-overwrite
   — has ONE owner; the walk memo and the transfer memo are
   instantiations.  See [cbat_memo.ml]'s header for the discipline's
   soundness argument (the ticket-03 version-oracle validity). *)

open Core_kernel
open Bap.Std

module type Value = sig
  type t
end

module Make (V : Value) : sig
  type value = V.t

  (* ONE entry: the stamped read-set (internal to the discipline) +
     the memoized value. *)
  type entry = {
    e_reads : (Tid.t * int) list;
    e_value : value;
  }

  type t = entry Tid.Map.t Tid.Map.t

  val empty : t

  (* The entry is reusable: every recorded (block, version) still
     matches — no block the computation read has changed state.
     [version] is the run context's oracle ([ver_of], partially
     applied) — threaded per call, never captured, so the memo stays
     pure and the context stays the single owner of state. *)
  val valid : version:(Tid.t -> int) -> entry -> bool

  (* The version-stamped read-set of the computation that just
     finished. *)
  val stamp : version:(Tid.t -> int) -> Tid.Set.t -> (Tid.t * int) list

  (* The memoized value iff the entry exists and is still valid. *)
  val find :
    version:(Tid.t -> int) -> t -> Tid.t -> Tid.t -> value option

  (* Record the value with its read-set (stamped here). *)
  val add :
    version:(Tid.t -> int) ->
    t -> Tid.t -> Tid.t -> reads:Tid.Set.t -> value -> t
end
