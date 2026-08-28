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

(* * This module implements Circular Linear Progressions in the style of [1] "Executable Analysis using Abstract Interpretation with Circular Linear Progressions". *)

type t [@@deriving bin_io, sexp]

include Cbat_wordset_intf.S with type t := t

val create : ?width:int -> ?step:word -> ?cardn: word -> word -> t

(* [interval ~width ~lo ~hi]: the step-1 CLP [lo, hi] — the span cardinality via [cardn_from_bounds] (a wrapped pair, lo > hi, is the CIRCULAR interval — the [circular_hull] semantics; no full-domain gate here, the composite callers apply theirs). *)
val interval : width:int -> word -> word -> t

val nearest_pred : word -> t -> word option
val nearest_succ : word -> t -> word option

val is_top : t -> bool
val is_infinite : t -> bool
val is_bottom : t -> bool

val subset : t -> t -> bool

(* * [widen_join_threshold ladder p1 p2] — thresholded widening (the Astrée-style bounded extrapolation; docs/widening-thresholds-plan.md). *)
val widen_join_threshold : word list -> t -> t -> t



