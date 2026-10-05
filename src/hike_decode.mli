(* Internal BAP adapter for the discovery pass. *)
open Bap.Std

type out = {
  grown : Disasm.Driver.state;
  cfg : Graphs.Cfg.t;
  subs : Disasm.Subroutines.t;
}
val file_of : program term -> string
val initial : Project.t -> out
val program_of_state : Disasm.Driver.state -> Disasm.Subroutines.t -> program term
val rescan : Project.t -> file:string -> roots:int64 list -> out option
val terminators : Graphs.Cfg.t -> (Addr.t * Addr.t) list
