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

(* Offset-from-origin expression of a frame-derived register. *)
type frame_term = {
  fconst : WordSet.t;               (* constant part *)
  fvars : (var * int) list;         (* scaled non-derived registers *)
}
type frame = (var * frame_term) list

(* Frame relation of a state; None is bottom. *)
val frame_of : t -> frame option

(* State with the frame replaced. *)
val set_frame : t -> frame option -> t

(* Entry-state frame: entry RSP has offset 0. *)
val seed_frame : frame option

(* Restore RSP's offset by +8. *)
val frame_add_rsp : frame option -> frame option

(* Bil-free frame ops. *)
val frame_key : var -> var
val frame_lookup : frame -> var -> frame_term option
val frame_remove : frame -> var -> frame
val frame_set : frame -> var -> frame_term -> frame
val frame_add_const : frame_term -> WordSet.t -> frame_term
val frame_sub_const : frame_term -> WordSet.t -> frame_term
val frame_add_fvar : frame_term -> var -> int -> frame_term

val add_word : t -> key:var -> data:WordSet.t -> t
val add_memory : t -> key:var -> data:Cbat_ai_memmap.t -> t

val find_word : WordSet.idx -> t -> var -> WordSet.t
val find_memory : Cbat_ai_memmap.idx -> t -> var -> Cbat_ai_memmap.t

val selective_widen_extrapolate : ?head:Tid.t option -> need:Var.Set.t -> steps:int -> t -> t -> t

(* Keep [preserved] words, top the rest and all memory. *)
val call_abstraction : preserved:Var.Set.t -> t -> t

(* Like [call_abstraction]; keeps cells at key >= [rsp] outside [escape]. *)
val call_abstraction_frame : preserved:Var.Set.t -> rsp:WordSet.t
  -> escape:WordSet.t list -> t -> t
