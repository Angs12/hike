(* The drive loop's re-decode: one decode context over the program's own
   file and the discovered entries as [is_subroutine] facts.  The
   resolved dispatch destinations ride the instruction labels' own
   [Insn.Slot.dests] facts (provided by the run, monotone), so the
   driver keeps decoding at the addresses the VSA resolved; BAP's own
   partition assigns every decoded block to its owning entry. *)

open Bap.Std

type out = {
  grown : Disasm.Driver.state;
  cfg : Graphs.Cfg.t;
  subs : Disasm.Subroutines.t;
}

(* The file the program was lifted from (the decode context's package
   and unit name). *)
val file_of : program term -> string

(* The program of a grown decode: BAP's own lift of the partition, so
   every sub the decode and the partition name is in it. *)
val program_of_state : Disasm.Driver.state -> Disasm.Subroutines.t -> program term

(* The code regions of the project's memory, in memmap order. *)
val code_mems : Project.t -> mem list

(* One re-scan under the file's own decode context: durable
   [is_subroutine] facts on the roots (the partition's entries) and the
   entry promise over the roots (the scan's classification).  [None]
   when the knowledge computation produced nothing. *)
val rescan : Project.t -> file:string -> roots:int64 list -> out option

(* The cfg nodes reachable from the block at [a]. *)
val closure_at : Graphs.Cfg.t -> Addr.t -> Graphs.Cfg.node list

(* Each decoded block's start address and its terminator instruction's
   address: the driver's dests facts key on the instruction label, while
   a solver-rewritten jmp carries no [address] attr. *)
val terminators : Graphs.Cfg.t -> (Addr.t * Addr.t) list

(* A destination label's address fact, the channel BAP's own
   [collect_dests] resolves through; [None] for a name-only label (an
   external, an intrinsic). *)
val label_addr : Tid.t -> int64 option
