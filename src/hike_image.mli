(* The ELF-image readers (see hike_image.ml). *)

open Bap.Std

type region = { addr : int64; size : int64; name : string }

val get_section_mem : string -> Project.t -> (Memory.t * Value.t) option

val get_section_data :
  (Memory.t * Value.t) option -> (Bytes.t * Word.t * Word.t) option

val get_copy_relocations :
  Project.t -> bss_addr:int64 -> bss_size:int64 -> (int * string) list

val get_relocated_words : Project.t -> int64 list

(** Every externally-relocated word: its site and the symbol whose
    address the dynamic linker binds there. *)
val external_references : Project.t -> (int64 * string) list

(** The load bias: memory-image addresses are the file vaddrs plus it. *)
val get_bias : Project.t -> int64

(** Every RELATIVE site with its runtime value: the loader's
    (site, addend) fact plus the bias. *)
val relative_values : Project.t -> bias:int64 -> (int64 * int64) list

(** One section's image fragments: a RELATIVE word takes its runtime
    value, an externally-relocated word is dropped, the rest keep the
    file bytes. *)
val substitute_relocated_words :
  bytes:Bytes.t ->
  lo:int64 ->
  hi:int64 ->
  relocated:int64 list ->
  relative:(int64 * int64) list ->
  (Bytes.t * int64 * int64) list

val get_section_images : Project.t -> (Bytes.t * int64 * int64) list

val get_named_region_info : Project.t -> region Base.Sequence.t
