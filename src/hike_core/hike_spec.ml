(* The section spec: the producer/emitter contract point, below both so
   [Hike_kb] and the emitter can share it without depending on each
   other. *)

(* Variant-II TLS layout from PT_TLS, including the first-byte alignment.
   [tls_lo] is the segment-line address of the first TLS byte; [tls_base]
   is the TP-relative offset of that byte (negative when the block sits
   below TP), and [tls_prefix] is the alignment padding before the image. *)
type tls_spec = {
  tls_lo : int64;
  tls_memsz : int64;
  tls_align : int;
  tls_base : int64;
  tls_prefix : int;
  tls_image : Bytes.t;
}

(* The components, the spans served whole (each (id, lo, hi)), the word
   grid, the input sections in the fixed section-list order ([None] =
   absent from the binary), the TLS block, and the loader's relocation
   facts: the RELATIVE words' runtime values (in-module addresses) and
   the externally-relocated words' symbols. *)
type section_spec = {
  spec_comps : Hike_stack_model.sec_comp list;
  spec_whole : (int * int64 * int64) list;
  spec_word : int;
  spec_sections : Hike_stack_model.sec_meta option list;
  spec_tls : tls_spec option;
  spec_relative : (int64 * int64) list;
  spec_externals : (int64 * string) list;
}
