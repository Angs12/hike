(* LLVM emitter. Signature collection and body emission both run inside
   [emit_program]; the emission state — one run ctx and a per-sub
   scope — is internal values, never global. *)

open Bap.Std
open Bap_core_theory

(** The FP lane's one home (the table, the signatures, the render). *)
module Fp = Bil2llvm_fp

(** The native FP op constructors: one definition, in the FP lane. *)
type native_fp = Bil2llvm_fp.native_fp

(** Intrinsic classification: does [name] map to a native FP op? *)
val native_fp_op : string -> native_fp option

(** The sub's LLVM name (tid-name sanitization). *)
val sanitize_name : string -> string

(** The signature pass, for the direct emitter callers (the fixtures):
    writes each sub's signature, with its lane types, onto its [arg]
    terms.  The pipeline runs it as [hike-sign]. *)
val sign_program :
  target:Bap_core_theory.Theory.Target.t ->
  program term ->
  program term

(** One owner of a byte range of a section: a component or a gap run.
    [own_id] is the component id ([None] for a gap run). *)
type sec_owner = Bil2llvm_env.sec_owner = {
  own_id : int option;
  own_lo : int64;               (* native byte range [own_lo, own_hi] *)
  own_hi : int64;
  base : Llvm.llvalue;
  (* The component's emission decision (components only). *)
  typed_w : int;                (* bytes per element: 8/4/2/1 *)
}


(** One section of the emitted module: the base global, the native
    span, the byte image, and the byte-exact owner tiling.  Empty
    [owners] = the identity (the one big array in [base]). *)
type section = Bil2llvm_env.section = {
  base : Llvm.llvalue;
  min_addr : word;
  max_addr : word;
  bytes : Bytes.t option;
  owners : sec_owner list;
}

(** The section vocabulary: the model's [sec], whose data sections
    carry the section table. *)
type section_type = Bil2llvm_env.section_type

(** One input section of the spec: a byte-image section or the bss span. *)
type sec_meta = Hike_stack_model.sec_meta = {
  sm_type : section_type;
  sm_const : bool;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : Bytes.t option;
  sm_copy_relocs : (int * string) list;
}

(** The section spec: the components, the spans served whole
    (each (id, lo, hi)), the word grid, the input sections in the
    fixed section-list order ([None] = absent from the binary), and the
    absolute copy-relocation slot addresses used by access routing. *)
type section_spec = Bil2llvm_env.section_spec = {
  spec_comps : Hike_stack_model.sec_comp list;
  spec_whole : (int * int64 * int64) list;
  spec_word : int;
  spec_sections : sec_meta option list;
  spec_copy_relocs : int64 list;
}

(** Constructs the sections from the spec.  Gap-run names draw from
    one counter across sections, consumed in the fixed tiling order. *)
val build_sections :
  Llvm.llcontext -> Llvm.llmodule -> section_spec -> Bil2llvm_env.section list

(** The emission entry: builds the sections from [spec], then runs
    signature collection and body emission over [prog].  Output is
    the side effect on [llvm_module]. *)
val emit_program :
  Llvm.llcontext ->
  Llvm.llmodule ->
  target:Theory.Target.t ->
  addr_bits:int ->
  symtab:Symtab.t option ->
  section_spec ->
  program term ->
  unit
