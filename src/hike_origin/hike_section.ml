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

(* A loaded range's runtime write permission, from the program headers:
   [Read_only] lies in a PT_LOAD without PF_W, [Relro] in a PT_GNU_RELRO
   range (written only by the loader's relocation), [Writable] is any
   other byte. *)
type access = Read_only | Relro | Writable
[@@deriving bin_io, equal, compare, sexp]
