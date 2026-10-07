(* The section vocabulary, denotation predicates, and the shared
   stack/var/layout contracts used by the attribution, the passes, and
   the emitter.  The producer/emitter contract point. *)

open Bap.Std
open Bap.Std.Bil.Types
module Abi = Hike_abi

(* The sections in declaration order: the shared [Hike_section] ADT. *)
type sec = Hike_section.t =
  | Stack
  | Args
  | Vla
  | Text
  | Rodata
  | Data
  | Got
  | Gotplt
  | Datarelro
  | Bss

val equal_sec : sec -> sec -> bool
val compare_sec : sec -> sec -> int
val sexp_of_sec : sec -> Base.Sexp.t
val sec_of_sexp : Base.Sexp.t -> sec

(* The section's ELF name — the one spelling of the name grammar. *)
val sec_name : sec -> string

(* The def-carried classification: the occupied extent or the
   justified unbounded form. *)
module Tag : sig
  type t =
    | Range of int64 * int64
    | Unbounded

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val sexp_of_t : t -> Base.Sexp.t
  val t_of_sexp : Base.Sexp.t -> t
end

type sec_tag = Tag.t

(* The ABSOLUTE position of the entry RSP on the segment line. *)
val segment_base : int64

(* The clamp and its bounds, shared with the call abstraction. *)
val caller_window_bytes : int64
val stack_max : int64
val stack_floor : entry:int64 -> int64
val args_ceiling : int64
val positions_of_offsets : Cbat_clp_set_composite.t -> (int64 * int64) option
val unsigned_bounds : Cbat_clp_set_composite.t -> (int64 * int64) option
val full_bounds :
  Cbat_clp_set_composite.t -> flo:int64 -> cei:int64 -> int64 -> int64 -> int64 * int64
val escape_extent :
  entry:int64 -> Cbat_clp_set_composite.t -> (int64 * int64) option
val key_extent : Cbat_clp_set_composite.t -> (Cbat_word.t * Cbat_word.t) option

val args_base : entry:int64 -> word:int -> int64
val stack_top : entry:int64 -> word:int -> int64

(* The ONE caller-window denotation. *)
val is_window_denotation :
  entry:int64 -> word:int -> Cbat_clp_set_composite.t -> bool

val expand_hi : cap:int64 -> int64 -> int -> int64
val expand_hi_unsigned : int64 -> int -> int64
val clip :
  cmp:(int64 -> int64 -> int) ->
  int64 -> int64 -> int64 -> int64 -> (int64 * int64) option

val singleton_i64 : Cbat_clp_set_composite.t -> int64 option
val singleton_offset : Cbat_clp_set_composite.Clp.t -> int64 option
val singleton_stack_position : Cbat_clp_set_composite.t -> int64 option

(* The return-address fact and its projections. *)
val is_return_address : Cbat_clp_set_composite.t -> bool
val is_return_address_tag : sec_tag -> bool
val is_return_address_shape : abi:Abi.t -> exp -> bool

(* The storage a ptr-kind value lives in. *)
type ptr_storage =
  | Ptr_region of int
  | Ptr_residue
  | Ptr_window
  | Ptr_vla

val equal_ptr_storage : ptr_storage -> ptr_storage -> bool

(* One def, one memory node — structural, so the emitter's
   constructors pattern-match it. *)
(* One def, one memory node. *)
type mem_node = [ `Load of exp * exp * Size.t
                | `Store of exp * exp * exp * Size.t ]

val mem_node_of : exp -> mem_node option

val mem_node_count : exp -> int
val reads_mem : exp -> bool
val addr_of_rhs : exp -> (exp * Size.t) option
val store_data_of_rhs : exp -> exp option

(* BAP term reads plus ABI transfer boundary reads, split by direction:
   the inputs the transfer consumes from the containing sub (a call's
   parameter registers) vs the outputs the convention produces (the
   return registers; a sub's entry lanes read inputs only). *)
val def_reads : def term -> Var.Set.t
val phi_reads : phi term -> Var.Set.t
val phi_reads_from : phi term -> Tid.t -> Var.Set.t
val jmp_operand_reads : jmp term -> Var.Set.t
val jmp_boundary_reads : abi:Abi.t -> jmp term -> Var.Set.t
val jmp_boundary_inputs : abi:Abi.t -> jmp term -> Var.Set.t
val jmp_input_reads : abi:Abi.t -> jmp term -> Var.Set.t
(* The mem-typed defs a call-bearing block hands its callee: the
   storages the site's stores built and the call-argument address
   temps. *)
val blk_boundary_reads : blk term -> Var.Set.t
(* The FP call site's argument temp ([intrinsic:xN[:width]]). *)
val jmp_reads : abi:Abi.t -> jmp term -> Var.Set.t
val jmp_target_reads : jmp term -> Var.Set.t
val def_writes : def term -> Var.Set.t
val phi_writes : phi term -> Var.Set.t
val blk_free_vars : blk term -> Var.Set.t
val word_bits : int -> int
val is_true_cond : exp -> bool

(** The one thread-pointer offset rule: whether an address expression
    is the thread pointer plus a byte offset (an affine analysis in the
    pointer).  [Tp_based (Some o)] — the pointer plus the constant [o];
    [Tp_based None] — the pointer plus a dynamic pointer-free offset;
    [Tp_nonlinear] — the expression reads the pointer but is not
    pointer-plus-offset (a width-changing cast, a non-unit coefficient);
    [Tp_absent] — the pointer never occurs. *)
type tp_offset = Tp_absent | Tp_based of int64 option | Tp_nonlinear

val tls_tp_offset : tp:var -> exp -> tp_offset

(* The signature contract. *)
val is_intrinsic : sub term -> bool
val is_emittable_intrinsic : sub term -> bool
(** The program's main, stamped by the producer from the entry's
    denotation; the C-ABI export the native crt1 calls. *)
val main_role : unit Value.Tag.t

val fixed_signature : sub term -> bool

val arg_slot : addr_bits:int -> int -> var
val call_arg : addr_bits:int -> int -> var
val is_call_arg : var -> bool
val is_arg_slot : var -> bool

val window_mem : addr_bits:int -> var
val is_window_mem : var -> bool

val hike_window_var : word:int -> var
val is_window_var : var -> bool

val region_name : int -> string
val residue_id : int

(* Slot geometry. *)
val slot_offset : word:int -> int -> int64
val slot_index_of_offset : word:int -> int64 -> int
val args_cell_of_span : word:int -> entry:int64 -> int64 -> int64 -> int option

val region_mem : addr_bits:int -> int -> var

val region_ptr : addr_bits:int -> int -> var
val is_region_ptr : var -> bool

val vla_ptr : addr_bits:int -> Tid.t -> var
val is_vla_ptr : var -> bool

val sec_comp_ptr : addr_bits:int -> int -> var
val is_sec_comp_ptr : var -> bool

(* The un-carved global memory state: BAP's own [mem] var; its stores
   cross sub boundaries. *)
val is_global_mem : var -> bool

val is_storage_base : var -> bool
val region_ptr_id_of : var -> int option

val is_mem : var -> bool
val is_region_mem : var -> bool
type sec_comp = {
  comp_id : int;
  sec_lo : int64;
  sec_hi : int64;
  lo_w : int;
  hi_w : int;
  typed_w : int;
}

(* One data section's row — the fixed-table facts the attribution and
   the emitter both read.  [sm_image] is None for the bss region. *)
type sec_meta = {
  sm_type : sec;
  sm_const : bool;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : Bytes.t option;
  sm_copy_relocs : (int * string) list;
}

val sec_comp_name : int -> string
val sec_comp_mem : addr_bits:int -> int -> var
val sec_res_name : int -> string
val is_sec_comp_mem : var -> bool

(* The tid-name sanitization. *)
val sanitize_tid_name : string -> string

val sub_map : program term -> sub term Tid.Map.t
val sub_reads : abi:Abi.t -> sub term -> Var.Set.t
val deepest_sp_decrement : sub term -> abi:Abi.t -> int64

(* The call facts. *)
val machine_call : jmp term -> bool
val call_pushes : jmp term -> bool
val has_call_push : sub term -> bool

(* The lifted va_list construction: the proof a sub is variadic. *)
val is_variadic_construction :
  abi:Abi.t ->
  entry:int64 ->
  denote:(blk:blk term -> ?def:def term -> exp ->
           (Cbat_clp_set_composite.t, Type.error) Result.t) ->
  sub term ->
  bool

(* The layout: every alloca of the sub, riding the sub term. *)
module Sub_layout : sig
  type region = {
    r_id : int;
    r_lo : int64;
    r_hi : int64;
    r_bytes : int64;
  }

  val equal_region : region -> region -> bool
  val compare_region : region -> region -> int
  val sexp_of_region : region -> Base.Sexp.t
  val region_of_sexp : Base.Sexp.t -> region

  type t = {
    regions : region list;
    window_param : bool;
  }

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val sexp_of_t : t -> Base.Sexp.t
  val t_of_sexp : Base.Sexp.t -> t

  val pp : Format.formatter -> t -> unit
end

type layout_region = Sub_layout.region = {
  r_id : int;
  r_lo : int64;
  r_hi : int64;
  r_bytes : int64;
}

type sub_layout = Sub_layout.t = {
  regions : Sub_layout.region list;
  window_param : bool;
}

val layout_tag : Sub_layout.t Value.Tag.t

(* The SSA pass's block stamp. *)
module Versions : sig
  type t = {
    args : (var * var) list;
    rets : (var * var) list;
    entry : (var * var) list;
  }

  val compare : t -> t -> int
  val sexp_of_t : t -> Base.Sexp.t
  val t_of_sexp : Base.Sexp.t -> t

  val pp : Format.formatter -> t -> unit
end

val versions_tag : Versions.t Value.Tag.t
val ssa_tag : unit Value.Tag.t
val is_ssa : sub term -> bool
val set_layout : sub_layout -> sub term -> sub term

(* The variadic stamp: the sub's body holds the lifted va_list
   construction. *)
val is_variadic : sub term -> bool
val set_variadic : sub term -> sub term

(* The emission signature rides the sub's own arg terms. *)
val set_sig : sub term -> Arg.t list -> sub term
val is_ret : Arg.t -> bool
val sig_args : sub term -> Arg.t list
val sig_rets : sub term -> Arg.t list

(* The lane type/kind flags on the arg terms. *)
module Flag : sig
  (* The boolean stamp. *)
  type t = bool

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val sexp_of_t : t -> Base.Sexp.t

  val pp : Format.formatter -> t -> unit
end

val is_ptr_arg : Arg.t -> bool
val set_ptr_arg : Arg.t -> Arg.t

val is_arg_ptr_kind : Arg.t -> bool
val set_arg_ptr_kind : Arg.t -> Arg.t

(* The PLT-trampoline stamp. *)
val is_plt_trampoline_sub : sub term -> bool
val set_plt_trampoline : sub term -> sub term

(** The self-call stub's shape: a self-targeted direct call, a real
    call jmp, and reads confined to SP and the return registers.  One
    rule, here with the tag it produces; the sign pass stamps it. *)
val is_self_call_shape :
  target:Bap_core_theory.Theory.Target.t -> sub term -> bool

(** The declaration classification: the prune's leave census and the
    sign pass's self-call shape stamp the trampoline tag; a bodyless
    sub, and a sub named by a loader relocation ([reloc_names]), are
    declarations too.  One predicate for every consumer. *)
val is_declared : ?reloc_names:Core.String.Set.t -> sub term -> bool
