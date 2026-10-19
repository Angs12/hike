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

type scalar_store

val create_scalars :
  variables:var list -> blocks:(tid * Var.Set.t) list -> seed:t -> scalar_store

(* The edge's own bindings: the destination's incoming phi values, read
   from this state's surviving bindings or from the definitions' cells. *)
val project : keep:Core.Int.Set.t -> block:tid -> t -> t

(* The block's env keeps its own incoming phi values and its memory; the
   definitions' values live in the cells. *)
val enter_block : scalar_store -> tid -> t -> t

(* A temporary walk's private cells: [copy_scalars e] gives [e] its own
   copy of the shared cell array, so writes through it cannot reach the
   store every permanent state shares.  [adopt_scalars ~from e] puts [e]
   on [from]'s store, keeping [e]'s block, so two states of one walk
   share the private cells. *)
val copy_scalars : t -> t
val adopt_scalars : from:t -> t -> t

(* Drop block-local word/slice bindings a caller-supplied entry may have
   left behind after a def; the definitions' cells own those values. *)
val scalar_snapshot : t -> t

include Cbat_lattice_intf.S_val with type t := t

(* Stack provenance is the WORD value itself: the entry RSP's word
   carries the symbolic segment base. *)

(* A redefinition: the word is overwritten and the owner's slices, which
   describe its previous value, are discarded. *)
val add_word : t -> key:var -> data:WordSet.t -> t

(* A narrowing of the word's current value: its slices stay valid. *)
val refine_word : t -> key:var -> data:WordSet.t -> t
val add_memory : t -> key:var -> data:Cbat_ai_memmap.t -> t

val find_word : WordSet.idx -> t -> var -> WordSet.t
val find_memory : Cbat_ai_memmap.idx -> t -> var -> Cbat_ai_memmap.t

(* The fact about bits [lo..hi] of the variable's current value, of width
   [hi - lo + 1]; top when none is recorded. *)
val find_slice : t -> var -> hi:int -> lo:int -> WordSet.t

(* Overwrite the slice; callers meet with what is known.  A range that is
   out of bounds or a set of another width is ignored. *)
val add_slice : t -> var -> hi:int -> lo:int -> data:WordSet.t -> t

(* The slices of [from] met into the state: the edge refinement rebuilds
   the block-end state forward and carries the guard's slices across. *)
val carry_slices : from:t -> t -> t
val copy_slices : from:t -> source:var -> target:var -> t -> t

(* The frame has escaped: a stack address may be held where a callee
   reaches it, so a call keeps no stack cell.  A path fact that joins by
   OR and never clears within a sub; [bottom] and the entry state have it
   clear.  The first form of the call-escape design's carried set (T36);
   a region set grows from it. *)
val frame_escaped : t -> bool
val escape_frame : t -> t

val selective_widen_extrapolate : head:Tid.t -> landmarks:Cbat_landmarks.t -> need:Core.Int.Set.t -> steps:int -> t -> t -> t

(* The head's arm is Zero: advance-and-join per key. *)
val advance_join_landmarks : head:Tid.t -> landmarks:Cbat_landmarks.t -> need:Core.Int.Set.t -> t -> t -> t

(* No head-level steps: the keys widen, each still reading its own row. *)
val widen_with_landmarks : head:Tid.t -> landmarks:Cbat_landmarks.t -> need:Core.Int.Set.t -> t -> t -> t

(* Top every word key not in [preserved]; the memories stay. *)
val top_words_except : preserved:Core.Int.Set.t -> t -> t

(* Apply [f] to every memory cell; the words stay. *)
val map_memories : t -> f:(key:var -> data:Cbat_ai_memmap.t -> Cbat_ai_memmap.t) -> t

(* The whole-memory-top fallback; the words stay. *)
val top_memories : t -> t

#ifdef VSA_DEBUG
(* The per-visit witness for the fixpoint's churn diagnosis, and the
   count of the bindings that differ in representation alone. *)
val diff : t -> t -> string * int

(* Every word binding, tagged and printed, in one line. *)
val head_summary : t -> string
#endif
