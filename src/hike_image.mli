(* The ELF-image readers (see hike_image.ml). *)

open Bap.Std

type region = { addr : int64; size : int64; name : string }

val get_section_mem : string -> Project.t -> (Memory.t * Value.t) option

val get_section_data :
  (Memory.t * Value.t) option -> (Bytes.t * Word.t * Word.t) option

val get_copy_relocations :
  Project.t -> bss_addr:int64 -> bss_size:int64 -> (int * string) list

(** Every externally-relocated word: its site and the symbol whose
    address the dynamic linker binds there. *)
val external_references : Project.t -> (int64 * string) list

(** The image's entry address. *)
val entry_point : Project.t -> int64 option

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
  word:int ->
  (Bytes.t * int64 * int64) list

(** The never-written runtime ranges with their access: read-only
    PT_LOAD segments ([Read_only]) and the page-rounded PT_GNU_RELRO
    ranges ([Relro]), inclusive. *)
val protections :
  Project.t -> page:int64 -> (int64 * int64 * Hike_section.access) list

(** The access of the bytes [lo, hi]: the protection of a range covering
    them wholly, otherwise [Writable]. *)
val access :
  (int64 * int64 * Hike_section.access) list -> lo:int64 -> hi:int64 ->
  Hike_section.access

(** The fragments of an image inside the given ranges. *)
val clip_image :
  Bytes.t * int64 * int64 -> (int64 * int64) list -> (Bytes.t * int64 * int64) list

(** The images the analysis may read: relocated sections restricted to
    the never-written ranges. *)
val get_section_images : Project.t -> page:int64 -> (Bytes.t * int64 * int64) list

val get_named_region_info : Project.t -> region Base.Sequence.t

(** A section's runtime access under the protections; a section with no
    bytes is [Writable]. *)
val section_access :
  (int64 * int64 * Hike_section.access) list -> Project.t -> Hike_section.t ->
  Hike_section.access

(** PT_TLS layout and file image; missing facts or unreadable bytes are errors. *)
val tls_spec : Project.t -> Hike_spec.tls_spec option
