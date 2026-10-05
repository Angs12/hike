(* The section spec: the producer/emitter contract point, below both so
   [Hike_kb] and the emitter can share it without depending on each
   other. *)

(* The components, the spans served whole (each (id, lo, hi)), the word
   grid, the input sections in the fixed section-list order ([None] =
   absent from the binary), and the loader's relocation facts: the
   RELATIVE words' runtime values (in-module addresses), the
   externally-relocated words' symbols, and the absolute
   copy-relocation slot addresses used by access routing. *)
type section_spec = {
  spec_comps : Hike_stack_model.sec_comp list;
  spec_whole : (int * int64 * int64) list;
  spec_word : int;
  spec_sections : Hike_stack_model.sec_meta option list;
  spec_relative : (int64 * int64) list;
  spec_externals : (int64 * string) list;
  (* Absolute addresses of copy-relocated slots, for access routing. *)
  spec_copy_relocs : int64 list;
}
