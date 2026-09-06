(* LLVM emitter. Signature collection and body emission both run inside
   [emit_program]; the KB context vars are internal. *)

open Bap.Std
open Bap_core_theory

(** The native FP op constructors. *)
type native_fp = FMUL | FADD | FSUB | FDIV | FREM | SFLOAT | SINT | FORDER | FHLT | ISNAN

(** Intrinsic classification: does [name] map to a native FP op? *)
val native_fp_op : string -> native_fp option

(** The emission entry: populates the emitter state, then runs signature
    collection (sub declarations) and body emission over [prog].
    Output is the side effect on [llvm_module]. *)
val emit_program :
  Llvm.llcontext ->
  Llvm.llmodule ->
  target:Theory.Target.t ->
  ptrsize:int ->
  symtab:Symtab.t option ->
  text_section:(int array * int64 * int64) option ->
  section_remap:(int64 * int64 * Llvm.llvalue) list ->
  copy_relocs:int64 list ->
  Convutils.section list ->
  program term ->
  unit

(** Declares a section global as [[n x i64]]. *)
val create_section_global :
  Llvm.llcontext -> Llvm.llmodule -> int -> string -> is_const:bool -> Llvm.llvalue

(** Fills a section global's initializer from raw bytes. *)
val set_section_initializer :
  Convutils.emit_ctx ->
  Llvm.llcontext ->
  Llvm.llmodule ->
  Llvm.llvalue ->
  int array ->
  int64 ->
  unit

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
  Llvm.llvalue

(** PLT trampoline test: no reg free-vars + a call. *)
val is_plt_trampoline : Convutils.emit_ctx -> sub term -> bool

(** Degraded-path frame geometry: (bytes, anchor index, max width, anchor
    byte index). *)
val degraded_dims :
  ?abi:Hike_abi.t -> sub term -> int64 * int64 * int64 * int64

(** Intrinsic facts shared with the filter pass. *)
val is_intrinsic : sub term -> bool
val is_emittable_intrinsic : sub term -> bool
val is_llvm_x86_intrinsic : sub term -> bool
