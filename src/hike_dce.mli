open Bap_core_theory
open Bap.Std

(** Preserve every load/store operation and its dependencies, including
    nested memory expressions. ABI boundary reads and escaped storages
    remain roots. Unused scalar defs and phis are swept by liveness. *)
val dce :
  target:Theory.Target.t ->
  escape_roots:Var.Set.t ->
  Bap.Std.sub Bap.Std.term ->
  Bap.Std.sub Bap.Std.term
