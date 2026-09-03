(* DCE pass. Exposes [dce] only. *)

open Bap_core_theory

(** [dce ~target sub]: rewrites the return epilogue, then sweeps unused defs. *)
val dce : target:Theory.Target.t -> Bap.Std.sub Bap.Std.term ->
  Bap.Std.sub Bap.Std.term
