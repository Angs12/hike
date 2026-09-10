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

open Bap.Std

module WordSet = Cbat_clp_set_composite

type t

include Cbat_lattice_intf.S_val with type t := t

(* The frame relation is DELETED (T3): stack provenance is the WORD
   value itself (the symbolic segment base, [WordSet.stack_word]). *)

val add_word : t -> key:var -> data:WordSet.t -> t
val add_memory : t -> key:var -> data:Cbat_ai_memmap.t -> t

val find_word : WordSet.idx -> t -> var -> WordSet.t
val find_memory : Cbat_ai_memmap.idx -> t -> var -> Cbat_ai_memmap.t

(* Drop dead virtual temps; machine regs are the ABI surface and stay. *)
val gc : t -> keep:Var.Set.t -> t

val selective_widen_extrapolate : ?head:Tid.t option -> need:Var.Set.t -> steps:int -> t -> t -> t

(* Keep [preserved] words, top the rest and all memory. *)
val call_abstraction : preserved:Var.Set.t -> t -> t

(* Like [call_abstraction]; keeps cells outside the callee's write
   range (at/above the call-time RSP's key bounds, minus the escape
   key ranges of pointer arguments). *)
val call_abstraction_frame : preserved:Var.Set.t -> rsp:WordSet.t
  -> escape:WordSet.t list -> t -> t
