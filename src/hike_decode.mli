(* Internal BAP adapter for the discovery pass. *)
open Bap.Std

(** The package the project's labels live in: the file it was loaded
    from. *)
val file_of : Project.t -> string

(** Each block's start address and its last instruction's address. *)
val terminators : Graphs.Cfg.t -> (Addr.t * Addr.t) list

(** Whether [a] lies in one of the project's code regions. *)
val in_code : Project.t -> int64 -> bool

(** A fresh decode of every code region in which every root in [roots]
    answers [is_subroutine] through the entry promise (address-keyed, so
    the full set is needed on each scan), plus every provided destination
    fact. *)
val scan : Project.t -> file:string -> roots:int64 list -> Disasm.Driver.state

(** Resumes the decode from [starts] over the regions holding them.  A
    start becomes a subroutine only when [subroutines] says it is a root. *)
val resume :
  ?subroutines:bool -> Project.t -> file:string -> roots:int64 list ->
  Disasm.Driver.state -> starts:int64 list -> Disasm.Driver.state

(** Records that [site]'s last instruction transfers to [dest]. *)
val provide_dest : file:string -> site:int64 -> int64 -> unit

(** Adds destination facts and decodes their reach and every pending root.
    [roots] carries all entries. The resumed state is verified against these
    facts, with a fresh scan as fallback; rejected data is already settled. *)
val grow :
  Project.t -> file:string -> roots:int64 list ->
  destinations:(int64 * int64) list -> Disasm.Driver.state -> Disasm.Driver.state

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

(** Keeps only the body [entry] reaches. Calls [keep_fall] once per
    reached call, before following its edges; a false answer removes
    its fallthrough. Unreached calls never invoke the callback. *)
val trim : Graphs.Cfg.t -> entry:Block.t -> keep_fall:(Block.t -> bool) -> Graphs.Cfg.t

(** The body lifted by BAP's sub lifter under [tid] and [name]. *)
val lift : file:string -> tid:Tid.t -> name:string -> Block.t -> Graphs.Cfg.t -> sub term

(** BAP's partition of a decode into subroutines and the symbol table
    naming them: the facts the project's own disassembly would hold. *)
val symtab : file:string -> Disasm.Driver.state -> Symtab.t
