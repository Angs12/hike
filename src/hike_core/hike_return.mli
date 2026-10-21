(* The CFG materializer's canonical return edge. *)
open Bap.Std

val is_target : tid -> bool
val is_jmp : jmp term -> bool
val create : unit -> jmp term
val create_ret : jmp_tid:tid -> unit -> jmp term
