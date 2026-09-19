(* LLVM emitter. Signature collection and body emission both run inside
   [emit_program]; the KB context vars are internal. *)

open Bap.Std
open Bap_core_theory

(** The native FP op constructors. *)
type native_fp = FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT
               | FCONVERT of int | FORDER | FHLT | ISNAN

(** Intrinsic classification: does [name] map to a native FP op? *)
val native_fp_op : string -> native_fp option

(** The sub's LLVM name (tid-name sanitization) — the emitter owns the
    minting; the VSA's target-name map and the fixtures share the fact. *)
val sanitize_name : string -> string

(** The phi-arity view: one count per (predecessor, target) term edge —
    the completed dispatch's conditional gotos are real BIR edges, and
    the rewrite's one-goto-per-target rule keeps a multi-word case at
    one incoming. *)
val edge_counts_of_sub :
  sub term -> (Tid.t, (Tid.t, int) Core.Hashtbl.t) Core.Hashtbl.t

(** One owner of a byte range of a section: a component or a gap run.
    [own_id] is the component id ([None] for a gap run). *)
type sec_owner = Bil2llvm_env.sec_owner = {
  own_id : int option;
  own_lo : int64;               (* native byte range [own_lo, own_hi] *)
  own_hi : int64;
  base : Llvm.llvalue;
  (* The component's emission decision (components only). *)
  typed_w : int;                (* bytes per element: 8/4/2/1 *)
  is_const : bool;
  bss : bool;
}

(** One section of the emitted module: the base global, the native
    span, the byte image, and the byte-exact owner tiling.  Empty
    [owners] = the identity (the one big array in [base]). *)
type section = Bil2llvm_env.section = {
  base : Llvm.llvalue;
  min_addr : word;
  max_addr : word;
  bytes : int array option;
  owners : sec_owner list;
}

(** The reserved data-section kinds. *)
type section_type = Bil2llvm_env.section_type =
  | DATA
  | RODATA
  | BSS
  | GOT
  | GOTPLT
  | RODATA_REL
  | TEXT

(** One input section of the spec: a byte-image section (its span, word
    count on the word grid, const-ness, image) or the bss span (zeroed
    storage with its copy-relocated slots). *)
type sec_input = Bil2llvm_env.sec_input =
  | Sec_bytes of {
      si_type : section_type;
      si_lo : int64;
      si_hi : int64;
      si_words : int;
      si_const : bool;
      si_image : int array;
    }
  | Sec_bss of {
      si_lo : int64;
      si_hi : int64;
      si_words : int;
      si_copy_relocs : (int * string) list;
    }

(** The section spec: the finalized data tree's Global components, the
    spans served whole (each (id, lo, hi) — the section's own image
    global is the id's storage), the section word grid, and the input
    sections in the fixed section-list order ([None] = absent from the
    binary) — the emitter constructs the sections from it. *)
type section_spec = Bil2llvm_env.section_spec = {
  spec_comps : Hike_stack_model.sec_comp list;
  spec_whole : (int * int64 * int64) list;
  spec_word : int;
  spec_sections : sec_input option list;
}

(** Constructs the sections from the spec: the component/gap-run
    globals, the byte-exact owner tiles, and the residue names — one
    counter across sections, consumed in the fixed tiling order. *)
val build_sections :
  Llvm.llcontext -> Llvm.llmodule -> section_spec -> Bil2llvm_env.section list

(** The emission entry: builds the sections from [spec], populates the
    emitter state, then runs signature collection (sub declarations)
    and body emission over [prog].  Output is the side effect on
    [llvm_module]. *)
val emit_program :
  Llvm.llcontext ->
  Llvm.llmodule ->
  target:Theory.Target.t ->
  ptrsize:int ->
  symtab:Symtab.t option ->
  copy_relocs:int64 list ->
  section_spec ->
  program term ->
  unit

(** Declares a section global as [n x iN], [word] bytes per cell. *)
val create_section_global :
  Llvm.llcontext -> Llvm.llmodule -> int -> string -> is_const:bool ->
  word:int -> Llvm.llvalue

(** Uninitialized byte-array global ([n x i8]). *)
val create_uninitialized_global :
  Llvm.llcontext -> Llvm.llmodule -> int64 -> string -> Llvm.llvalue

(** [bss]-backed global with copy-relocated symbol slots. *)
val create_copy_reloc_bss :
  Llvm.llcontext ->
  Llvm.llmodule ->
  int64 ->
  string ->
  (int * string) list ->
  word:int ->
  Llvm.llvalue

(** Intrinsic facts shared with the filter pass. *)
val is_intrinsic : sub term -> bool
val is_emittable_intrinsic : sub term -> bool

(** The sub's signature is fixed — the promotion does not define it
    (the emittable intrinsics and @main); the promote rewrite, the
    signature collection, and the twin rule read this one fact. *)
val fixed_signature : sub term -> bool
