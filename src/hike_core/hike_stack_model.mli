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
val frame_alloca_max : int64
val stack_floor : entry:int64 -> int64
val args_ceiling : int64
val positions_of_offsets : Cbat_clp_set_composite.t -> (int64 * int64) option
val unsigned_bounds : Cbat_clp_set_composite.t -> (int64 * int64) option
val full_bounds :
  Cbat_clp_set_composite.t -> flo:int64 -> cei:int64 -> int64 -> int64 -> int64 * int64
val escape_extent :
  entry:int64 -> Cbat_clp_set_composite.t -> (int64 * int64) option
val key_extent :
  width:int -> Cbat_clp_set_composite.t -> (Cbat_word.t * Cbat_word.t) option

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
val singleton_offset : Cbat_clp_set_composite.Clp.Pieces.t -> int64 option
val singleton_stack_position : Cbat_clp_set_composite.t -> int64 option

(* The return-address fact and its projections. *)
val is_return_address : Cbat_clp_set_composite.t -> bool
val is_return_address_tag : sec_tag -> bool

(* The storage a ptr-kind value lives in. *)
type ptr_storage =
  | Ptr_region of int
  | Ptr_residue
  | Ptr_window

val equal_ptr_storage : ptr_storage -> ptr_storage -> bool

(* One def, one memory node — structural, so the emitter's
   constructors pattern-match it. *)
type mem_node = [ `Load of exp * exp * Size.t
                | `Store of exp * exp * exp * Size.t ]

val mem_node_of : exp -> mem_node option

val mem_node_count : exp -> int
val reads_mem : exp -> bool
val addr_of_rhs : exp -> (exp * Size.t) option
val store_data_of_rhs : exp -> exp option

val phi_reads_from : phi term -> Tid.t -> Var.Set.t
(* The mem-typed defs a call-bearing block hands its callee: the
   storages the site's stores built and the call-argument address
   temps. *)
val blk_boundary_reads : Hike_synth.table -> blk term -> Var.Set.t
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
val is_call_arg : Hike_synth.table -> var -> bool
val is_arg_slot : Hike_synth.table -> var -> bool

val window_mem : addr_bits:int -> var
val is_window_mem : Hike_synth.table -> var -> bool

val hike_window_var : word:int -> var
val is_window_var : Hike_synth.table -> var -> bool

val region_name : int -> string
val residue_id : int

(* Slot geometry. *)
val slot_offset : word:int -> int -> int64
val slot_index_of_offset : word:int -> int64 -> int
val call_arg_slot : word:int -> call_sp:int64 -> start:int64 -> int option
val args_cell_of_span : word:int -> entry:int64 -> int64 -> int64 -> int option

val region_mem : addr_bits:int -> int -> var

val region_ptr : addr_bits:int -> int -> var
val is_region_ptr : Hike_synth.table -> var -> bool


val sec_comp_ptr : addr_bits:int -> int -> var
val is_sec_comp_ptr : Hike_synth.table -> var -> bool

val is_storage_base : Hike_synth.table -> var -> bool
val region_ptr_id_of : Hike_synth.table -> var -> int option

val is_mem : var -> bool
val is_region_mem : Hike_synth.table -> var -> bool
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
  sm_access : Hike_section.access;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : Bytes.t option;
  sm_copy_relocs : (int * string) list;
}

val sec_comp_name : int -> string
val sec_comp_mem : addr_bits:int -> int -> var
val sec_res_name : int -> string
val is_sec_comp_mem : Hike_synth.table -> var -> bool

(* A model-owned storage var: a fissioned memory family or a storage base. *)
val is_model_storage : Hike_synth.table -> var -> bool

(* The tid-name sanitization. *)
val sanitize_tid_name : string -> string

val sub_reads : sub term -> Var.Set.t
val deepest_sp_decrement : sub term -> abi:Abi.t -> int64

(* The call facts. *)
val machine_call : jmp term -> bool
val call_pushes : jmp term -> bool
val has_call_push : sub term -> bool

type call_arg_store = {
  sb_slot : int;
  sb_def : def term;
}

val site_bindings_of_sub_with_blocks :
  word:int ->
  sp:var ->
  denote:(blk:blk term -> ?def:def term -> exp ->
          (Cbat_clp_set_composite.t, Type.error) Result.t) ->
  sub term -> (call_arg_store list * blk term) Tid.Map.t

(* The layout: every alloca of the sub, riding the sub term. *)
module Sub_layout : sig
  type region = {
    r_id : int;
    r_lo : int64;
    r_hi : int64;
    r_bytes : int64;
  }

  type t = {
    regions : region list;
    window_param : bool;
    runtime_residue : bool;
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
  runtime_residue : bool;
}

val layout_tag : Sub_layout.t Value.Tag.t

(** Marks a block whose scalar terms were processed by SSA, including an
    empty block with no versioned definitions. *)
val ssa_tag : unit Value.Tag.t

val boundary_read : blk term -> var -> var option
val boundary_write : blk term -> var -> var option
val local_output : blk term -> var -> var option
val passed_version : blk term -> var -> var option

(** The version of base register [v] in effect after [blk]'s defs. *)
val version_at_end : blk term -> var -> var

val set_layout : sub_layout -> sub term -> sub term

(* The emission signature rides the sub's own arg terms. *)
val set_sig : sub term -> Arg.t list -> sub term
val is_ret : Arg.t -> bool
val sig_args : sub term -> Arg.t list
val sig_rets : sub term -> Arg.t list
val return_lanes : target:Bap_core_theory.Theory.Target.t -> sub term -> Arg.t list

(** Explicit operands and the implicit lanes carried by a BIR term. *)
module Term_effects : sig
  type t = { reads : var list; writes : var list }
end

val effects : jmp term -> Term_effects.t
(** The jmp's own effects, [None] when no pass has derived them.  The
    [effects] default is a pre-SSA convenience; an SSA consumer must
    distinguish it. *)
val effects_opt : jmp term -> Term_effects.t option
val reads :
  [< `Def of def term | `Phi of phi term | `Arg of arg term | `Jmp of jmp term ] ->
  Var.Set.t
val writes :
  [< `Def of def term | `Phi of phi term | `Arg of arg term | `Jmp of jmp term ] ->
  Var.Set.t
val prepare_effects :
  synth:Hike_synth.table -> abi:Abi.t -> callee:(Tid.t -> sub term option) -> sub term -> sub term
(** The per-block part of [prepare_effects]; [outgoing] is the sub-level
    return lane set (the SP and the signature's return operands). *)
val prepare_block_effects :
  synth:Hike_synth.table -> abi:Abi.t -> callee:(Tid.t -> sub term option) ->
  outgoing:var list -> blk term -> blk term
val map_effects : read:(var -> var) -> write:(var -> var) -> jmp term -> jmp term

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
