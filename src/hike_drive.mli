(* The program producer: discovery over the decoder's own scan (ADR 0032). *)
open Bap.Std

(** The discovered program, the analysis facts of its solves, and the
    symbol table of the initial decode.  The caller installs all three. *)
type result = {
  program : program term;
  facts : Hike_kb.facts;
  symtab : Symtab.t;
}

(** Loads [path] with the loader's image, memory and symbol facts and
    no backend disassembly: the project's program and symbol table are
    empty, and [run] supplies both. *)
val load : ?loader:string -> string -> Project.t Core.Or_error.t

(** Discovery over the project's initial decode, its subroutine
    partition and symbol table, and the worklist over them.  A project
    loaded without BAP's disassembly gets a fresh scan and BAP's
    partition and symbol table of it; one loaded with it reuses BAP's. *)
val run : signatures:Hike_signatures.db -> Project.t -> result
