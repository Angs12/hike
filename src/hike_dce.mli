(* DCE pass. Exposes [dce] only. *)

open Bap_core_theory

(** [dce ?roots ~target sub]: rewrites the return epilogue, then sweeps
    unused defs. [roots] names storage mem vars whose bytes escape this
    sub — their stores survive the sweep. *)
val dce : ?roots:Bap.Std.Var.Set.t ->
  target:Theory.Target.t -> Bap.Std.sub Bap.Std.term ->
  Bap.Std.sub Bap.Std.term
