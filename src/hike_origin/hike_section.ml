(* The section vocabulary: the stack-line storages and the loaded module
   sections.  Attribution, the emitter and the VSA's module origin share
   this one ADT. *)
open! Core

type t = Stack | Args | Vla | Text | Rodata | Data | Got | Gotplt | Datarelro | Bss
[@@deriving bin_io, equal, compare, sexp]

(* The section's ELF name — the one spelling of the name grammar. *)
let name = function
  | Stack -> "stack"
  | Args -> "args"
  | Vla -> "vla"
  | Data -> "data"
  | Rodata -> "rodata"
  | Bss -> "bss"
  | Got -> "got"
  | Gotplt -> "got.plt"
  | Datarelro -> "data.rel.ro"
  | Text -> "text"
