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

(** The section vocabulary: the model's [sec], whose data sections
    carry the section table. *)
type section_type = Bil2llvm_env.section_type

(** One input section of the spec: a byte-image section or the bss span. *)
type sec_meta = Hike_stack_model.sec_meta = {
  sm_type : section_type;
  sm_access : Hike_section.access;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : Bytes.t option;
  sm_copy_relocs : (int * string) list;
}

(** The section spec: one definition, owned by [Hike_spec]. *)
type section_spec = Hike_spec.section_spec

(** The emission entry: builds the sections from [spec], then runs
    signature collection and body emission over [prog].  Output is
    the side effect on [llvm_module]. *)
val emit_program :
  Llvm.llcontext ->
  Llvm.llmodule ->
  target:Theory.Target.t ->
  addr_bits:int ->
  symtab:Symtab.t option ->
  synth:Hike_synth.table ->
  signatures:Hike_signatures.t ->
  section_spec ->
  program term ->
  unit
