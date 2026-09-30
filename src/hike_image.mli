(* The ELF-image readers (see hike_image.ml). *)

open Bap.Std

type region = { addr : int64; size : int64; name : string }

val get_section_mem : string -> Project.t -> (Memory.t * Value.t) option

val get_section_data :
  (Memory.t * Value.t) option -> (Bytes.t * Word.t * Word.t) option

val get_copy_relocations :
  Project.t -> bss_addr:int64 -> bss_size:int64 -> (int * string) list

val get_relocated_words : Project.t -> int64 list

val get_section_images : Project.t -> (Bytes.t * int64 * int64) list

val get_named_region_info : Project.t -> region Base.Sequence.t
