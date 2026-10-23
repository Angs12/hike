(* Exact facts about declared external library functions, read from
   signature files the user supplies.

   A file is a sequence of S-expression entries, one per exported
   function of one library at one symbol version; the types are
   [Hike_sysv] types:

     ((library libc.so.6) (version GLIBC_2.2.5) (symbol strlen)
      (return Long)
      (params (((ty Pointer) (access Read_only) (captured false))))
      (memory (Argmem Read_only)))

   [return], [returned], [variadic], [noreturn], [memory] and each
   parameter's [access] and [captured] may be omitted.  An omitted entry
   claims nothing: no return value, no returned parameter, not variadic,
   returns normally, may touch any memory, and every pointer parameter
   may be written and kept. *)

(* How a callee may use the memory a pointer parameter names. *)
type access = Read_only | Write_only | May_write

type param = {
  ty : Hike_sysv.ctype;
  access : access;
  captured : bool;  (* the callee may keep the pointer past the call *)
}

(* The memory a function may touch: anything, only what its pointer
   parameters name (with that access), anything but only to read, or
   nothing. *)
type memory = Any | Argmem of access | Reads_any | None_

type record = {
  library : string;                (* the soname the import binds to *)
  version : string;                (* its symbol version *)
  symbol : string;
  return : Hike_sysv.ctype option; (* [None] = void *)
  returned : int option;           (* the parameter the call returns *)
  params : param list;
  variadic : bool;
  memory : memory;
  noreturn : bool;
}

(* The call's placement under the System V x86-64 convention.  It is
   defined only for that convention: [abi] carries it. *)
val place : abi:Hike_abi.t -> record -> Hike_sysv.call

(* The target's argument register [index]. *)
val integer_register : abi:Hike_abi.t -> int -> Bap.Std.var option
val vector_register : abi:Hike_abi.t -> int -> Bap.Std.var option

(* Whether a value of the type may hold a pointer: it is, or contains, a
   pointer. *)
val carries_pointer : Hike_sysv.ctype -> bool

(* The entries of the user's files. *)
type db

val empty : db

(* The number of entries. *)
val cardinal : db -> int

(* A database of the given records. *)
val of_records : record list -> db

(* The entries of the files, a later file overriding an earlier entry
   of the same library, version and symbol. *)
val load : string list -> db Core.Or_error.t

(* The entries of one file's text. *)
val of_string : string -> db Core.Or_error.t

(* A per-lift record source.  [imports name] is the library and symbol
   version the binary binds the dynamic import [name] to; a record
   applies only on an exact match of library, version and symbol.
   Records describe the x86-64 System V ABI on GNU/Linux: any other
   [target] fails. *)
type t

val create :
  target:Bap_core_theory.Theory.Target.t -> db ->
  imports:(string -> (string * string) option) -> t

val find : t -> string -> record option
