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

type t

include Cbat_wordset_intf.S with type t := t

val is_top : t -> bool
val is_bottom : t -> bool
val is_infinite : t -> bool

val of_clp : Cbat_clp.t -> t

(* * [widen_join_threshold ladder t1 t2] — thresholded widening (docs/widening-thresholds-plan.md); the composite-level mirror of [Cbat_clp.widen_join_threshold], re-bounded to the FinSet/Clp invariant. *)
val widen_join : t -> t -> t
val extrapolate_steps : steps:int -> t -> t -> t
val widen_join_threshold : Bap.Std.Word.t list -> t -> t -> t
