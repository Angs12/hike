(* Internal BAP adapter for the discovery pass. *)
open Bap.Std

(** The package the program's subs name as their source file. *)
val file_of : program term -> string

(** The loader's decode. *)
val initial : Project.t -> Disasm.Driver.state

(** Each block's start address and its last instruction's address. *)
val terminators : Graphs.Cfg.t -> (Addr.t * Addr.t) list

(** Provides [dest] as a destination fact on the instruction at [site]. *)
val provide_dest : file:string -> site:int64 -> int64 -> unit

(** A fresh decode of every code region, with [roots] as subroutine
    facts and every provided destination fact. *)
val scan : Project.t -> file:string -> roots:int64 list -> Disasm.Driver.state

(** One function's candidate graph from the decoded state: the blocks
    [entry] reaches without entering another entry, every edge kept. *)
val function_cfg :
  file:string -> Disasm.Driver.state -> entry:Addr.t ->
  is_entry:(Addr.t -> bool) -> Graphs.Cfg.t

(** What a destination label names: a code address, or a symbol with no
    address in the module (an external or an intrinsic). *)
type dest = Code of int64 | Symbol of string | Unknown

val dest : Tid.t -> dest

(** The destination labels the decode recorded on a block's last
    instruction. *)
val dests : Block.t -> Tid.t list

(** Whether a block ends in a call. *)
val is_call : Block.t -> bool

(** Whether the block's last instruction is its only one with
    semantics. *)
val transfers_only : Block.t -> bool

(** The block of [cfg] that starts at [addr]. *)
val block_at : Graphs.Cfg.t -> Addr.t -> Block.t option

(** The body: a call block's fallthrough stays only when [keep_fall]
    accepts it; then only what [entry] reaches stays. *)
val trim : Graphs.Cfg.t -> entry:Block.t -> keep_fall:(Block.t -> bool) -> Graphs.Cfg.t

(** The body lifted by BAP's sub lifter under [tid] and [name]. *)
val lift : file:string -> tid:Tid.t -> name:string -> Block.t -> Graphs.Cfg.t -> sub term
