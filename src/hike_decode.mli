(* Internal BAP adapter for the discovery pass. *)
open Bap.Std

type out = {
  grown : Disasm.Driver.state;
  cfg : Graphs.Cfg.t;
  subs : Disasm.Subroutines.t;
}
val file_of : program term -> string
val initial : Project.t -> out
val program_of_state : file:string -> Disasm.Driver.state -> Disasm.Subroutines.t -> program term
val rescan : Project.t -> file:string -> roots:int64 list -> out option
val terminators : Graphs.Cfg.t -> (Addr.t * Addr.t) list

(** The jump that ends a block, if the decode recorded one. *)
val terminator_jump : Disasm.Driver.state -> Block.t -> Disasm.Driver.jump option

(** One function's candidate graph from the decoded state: the blocks
    [entry] reaches without entering another entry, every edge kept. *)
val function_cfg :
  file:string -> Disasm.Driver.state -> entry:Addr.t ->
  is_entry:(Addr.t -> bool) -> Graphs.Cfg.t

(** Each call block with its decoded destinations. *)
val calls : Disasm.Driver.state -> Graphs.Cfg.t -> (Block.t * Addr.t list) list

(** The body: a call's fallthrough stays only when [keep_fall] accepts
    its destinations; then only what [entry] reaches stays. *)
val trim :
  Disasm.Driver.state -> Graphs.Cfg.t -> entry:Block.t ->
  keep_fall:(Addr.t list -> bool) -> Graphs.Cfg.t

(** The body lifted by BAP's sub lifter under [tid] and [name]. *)
val lift : file:string -> tid:Tid.t -> name:string -> Block.t -> Graphs.Cfg.t -> sub term
