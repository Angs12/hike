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

(* WYSINWYX-2 — the a-priori frame relation carried IN the abstract state): a frame-derived register's offset-from-origin expression (origin = the sub's entry RSP), with the MUST-fact lattice semantics ([frame option]:. *)
type frame_term = {
  fconst : WordSet.t;               (* constant part (CLP; usually a singleton) *)
  fvars : (var * int) list;         (* scaled non-derived registers *)
}
type frame = (var * frame_term) list

(* [frame_of e]: the state's frame relation (None = the vacuous bottom state — the join identity). *)
val frame_of : t -> frame option

(* [set_frame e f]: the state with the frame replaced (the transfer's write — see [Cbat_vsa.apply_frame_def]). *)
val set_frame : t -> frame option -> t

(* [seed_frame]: the entry-state frame — the ORIGIN definition: the sub's entry RSP has offset 0 (both anchored and unanchored runs). Seeded by [Cbat_vsa.init_sol]. *)
val seed_frame : frame option

(* [frame_add_rsp f]: the call-revert — RSP's offset restores by +8 (the L-E1 matched-pair semantics; applied at the call-abstraction site in cbat_vsa.ml). *)
val frame_add_rsp : frame option -> frame option

(* The transfer's frame ops (Bil-free; the def-shape logic lives in [Cbat_vsa.apply_frame_def]). *)
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
val fold_words : (Bap.Std.var -> WordSet.t -> 'a -> 'a) -> 'a -> t -> 'a

(* hike addition (docs/widening-thresholds-plan.md): the thresholded widen — THE widening of the production fixpoint. [ladders] is a (bitwidth -> sorted rung list) assoc; word and memory cells widen against their width's ladder, the frame relation keeps the widened join. *)
val widen_join_threshold : (int * Bap.Std.word list) list -> t -> t -> t

(* SiftAbs H3 — selective widen: only vars in [need] are widened, others joined. *)
val selective_widen_join_threshold : ?head:Tid.t option -> (int * Bap.Std.word list) list -> need:Var.Set.t -> t -> t -> t
val selective_widen_extrapolate : ?head:Tid.t option -> need:Var.Set.t -> steps:int -> t -> t -> t
val selective_widen : need:Var.Set.t -> t -> t -> t

(* SiftAbs H3 — selective fixpoint detection: only vars in [need] are checked. *)
val equal_need : need:Var.Set.t -> t -> t -> bool

(* P2d-1b (lane A) — Call-ABI abstraction of an abstract state: the `preserved` words (matched by [Var.same]) keep their value-sets, every other word is TOPed, and memory is set to TOP entirely (a red-zone partition is. *)
val call_abstraction : preserved:Var.Set.t -> t -> t

(* Hike addition (the call-abstraction precision lane): like [call_abstraction], but the caller's own frame survives — cells at key >= [rsp] (the call-time, post-push RSP) and outside every [escape] range are kept; the. *)
val call_abstraction_frame : preserved:Var.Set.t -> rsp:WordSet.t
  -> escape:WordSet.t list -> t -> t
