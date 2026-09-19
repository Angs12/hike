(* The section home: the project's native data-section facts and the
   ownership pass — [range_of_denotation] is the ONE mechanism turning
   an address denotation into occupied-byte portions in the represented
   spaces; the immutable visitor collects members into the two
   collection trees; finalization decides each merged range's storage
   and numbers it.  The finalized trees are the authoritative
   ownership representation. *)

open Bap.Std

(** The sections in declaration order (the shared model's
    vocabulary).  A range carries its section, so merging across
    sections is impossible: the section is part of the point
    ordering. *)
type sec = Hike_stack_model.sec [@@deriving equal, compare, sexp]

(** One represented data span: a data section's native address range
    and its copy-relocated slot addresses (externally-owned bytes). *)
type data_span = {
  ds_sec : sec;
  ds_lo : int64;               (* inclusive native span *)
  ds_hi : int64;
  ds_slots : int64 list;
}
[@@deriving equal, compare, sexp]

(** A point of the section-ordered line: the section plus its local
    position — the sub-local segment line for Stack/Args (the entry
    RSP at [entry]), the unsigned native address for data sections. *)
type point = { p_sec : sec; p_pos : int64 } [@@deriving sexp]

(** An inclusive occupied-byte range. *)
type range = { lo : point; hi : point } [@@deriving sexp]

(** The endpoint ordering: the section first, then the domain's numeric
    order (signed segment line for Stack/Args, unsigned addresses for
    data sections). *)
val compare_point : point -> point -> int
val compare : range -> range -> int
val equal_point : point -> point -> bool
val equal : range -> range -> bool

(** The point/range constructors. *)
val point : sec -> int64 -> point
val range : sec -> int64 -> int64 -> range

(** One membership fact: an access's occupied interval in one section,
    or an escape requirement.  [m_def] is absent for escapes. *)
type member = {
  m_sec : sec;
  m_lo : int64;                (* occupied interval, section-local *)
  m_hi : int64;
  m_sub : Tid.t;
  m_def : Tid.t option;
  m_width : int;               (* access width in bytes; 0 for escapes *)
  m_store : bool;
  m_identity : bool;           (* requires identity (shared) storage *)
}
[@@deriving equal, compare, sexp]

(** The finalized storage of one merged range (D2): a region of its
    section — id 0 is the stack's residue region (the anchor and the
    caller window), ids from 1 are independently carved; a data
    region's id keys a module-wide global, and a whole span is one
    data region whose extent is the span. *)
type storage =
  | Stack_region of int
  | Stack_residue
  | Data_region of int
  | Arg_slot of int
[@@deriving equal, compare, sexp]

(** The finalized binding payload: the storage decision and its
    members (deterministic order, newest first). *)
type range_storage = {
  storage : storage;
  members : member list;
}
[@@deriving equal, compare, sexp]

(** The finalized interval tree (BAP's [Interval_tree] over [range]). *)
module Tree :
  Bap.Std.Interval_tree.S with type key := range and type point := point

(** The sub-local tree (Stack + Args + escapes + identity members). *)
type sub_tree = range_storage Tree.t

(** The program tree (all subs' data-section members). *)
type data_tree = range_storage Tree.t

(** The slim def-carried classification (the shared model's [Tag]):
    the def's section with its ADDRESS bounds (not the tree's
    occupied-byte bounds), the justified unbounded form, the
    data-section anchoring, or Dead.  Absence is the identity. *)
module Tag = Hike_stack_model.Tag

type sec_tag = Hike_stack_model.sec_tag

(** The completed attribution: the finalized trees and the slim tags.
    A value threaded through the pass; no consumer reads partial
    state. *)
type ctx = {
  sub_trees : sub_tree Tid.Map.t;
  data_tree : data_tree;
  tags : sec_tag Tid.Map.t;
}

(** One projected portion of an access: the occupied interval in one
    represented space, with the access's conversion eligibility in
    that space. *)
type portion = {
  pt_sec : sec;
  pt_lo : int64;
  pt_hi : int64;
  pt_elig : bool;
}
[@@deriving equal, compare, sexp]

(** The ONE range mechanism: address normalization, occupied-byte
    extent formation, and section attribution/projection of one
    address denotation of [width] bytes.  Bottom yields no portion
    (the Dead tag); every reachable unknown address contributes its
    full possible range to each space it may intersect. *)
val range_of_denotation :
  word:int ->
  entry:int64 ->
  spans:data_span list ->
  rip:bool ->
  width:int ->
  Cbat_vsa.WordSet.t ->
  sec_tag option * portion list

(** The collector and finalizer: one immutable-visitor pass over the
    program (memory accesses, stored-data and parameter-register
    escapes through the [denote] seam), then the storage decisions and
    the deterministic numbering.  [entry] is the sub-local line's
    entry-RSP position. *)
(** The section-prep readers over the project's image. *)
type 'a region = { addr : int64; size : int64; info : 'a }

val get_section_mem : string -> Project.t -> (Memory.t * Value.t) option
val get_section_data :
  (Memory.t * Value.t) option -> (int array * Word.t * Word.t) option
val get_copy_relocations :
  Project.t -> bss_addr:int64 -> bss_size:int64 -> (int * string) list
val get_named_region_info : Project.t -> string region Base.Sequence.t

(** The collector and finalizer: one immutable-visitor pass over the
    program (memory accesses, stored-data and parameter-register
    escapes through the [denote] seam), then the storage decisions and
    the deterministic numbering.  [entry] is the sub-local line's
    entry-RSP position. *)
val attribute :
  word:int ->
  entry:int64 ->
  abi:Hike_abi.t ->
  spans:data_span list ->
  denote:(blk:blk term -> ?def:def term -> exp ->
          (Cbat_vsa.WordSet.t, Type.error) Result.t) ->
  program term ->
  ctx

(** The ownership query: the finalized binding owning [r]. *)
val storage_of_range : range_storage Tree.t -> range -> range_storage option

(** The escape-root mem vars: storages whose ranges carry identity
    members — bytes another world reads through an escaped address;
    their stores' reader is never a def of this sub. *)
val escape_roots_of_tree : sub_tree -> Var.Set.t

(** The slim tag read off the def's value; [set_sec_tag] stamps it. *)
val sec_tag : def term -> sec_tag option
val set_sec_tag : sec_tag -> def term -> def term

(** Stamps the ctx's slim tags onto the sub's defs (a term mapper). *)
val stamp_tags : ctx -> sub term -> sub term

(** The occupied range of a def's memory node at its own position in
    [blk]: the def's address denotation through the seam, projected by
    [range_of_denotation] — the Stage-B step-1 reading. *)

(** The promotion (the section home's producer products): the narrow
    per-sub facts, the callee-side window-traffic classification (the
    return-address set feeds the jmp-kind stamping), the caller-side
    resolution over the seam, and the BIR rewrite. *)
type facts = {
  prom_arity : int;
  prom_sites : Hike_stack_model.call_site Tid.Map.t;
  prom_resolved : Tid.t option Tid.Map.t;
}

(** The VLA event's shape: the defs whose SP move the code does not
    fix — a runtime-sized dynamic allocation (a pure BIR shape test;
    no denotation is read). *)
val dynamic_alloc_tids_of :
  sp:var ->
  denote:(blk:blk term -> ?def:def term -> exp ->
          (Cbat_vsa.WordSet.t, Type.error) Result.t) ->
  sub term -> Tid.Set.t

(** The caller side: the resolved indirect calls and the escaping
    SP-formed extents. *)
val caller_side :
  denote:(blk:blk term -> ?def:def term -> exp ->
          (Cbat_vsa.WordSet.t, Type.error) Result.t) ->
  symtab:Symtab.t option ->
  name_tid:(string * Tid.t) list ->
  abi:Hike_abi.t ->
  sub term -> Tid.t option Tid.Map.t * (int64 * int64) list

(** The resolution product alone. *)
val call_resolution :
  denote:(blk:blk term -> ?def:def term -> exp ->
          (Cbat_vsa.WordSet.t, Type.error) Result.t) ->
  symtab:Symtab.t option ->
  name_tid:(string * Tid.t) list ->
  abi:Hike_abi.t ->
  sub term -> Tid.t option Tid.Map.t

(** The promotion rewrite: the sub gains its promoted parameters as
    real BIR args, the sites' outgoing stores gain their call-arg defs,
    and singleton-resolved indirect targets become direct. *)
val promote_sub :
  abi:Hike_abi.t -> facts -> sub term -> sub term

(** The T2 rewrite surface. *)

(** The sub's layout from its finalized tree: the Region components'
    geometry and the fallback frame (S24/S15). *)
val layout_of_tree :
  word:int ->
  entry:int64 ->
  abi:Hike_abi.t ->
  sub:sub term ->
  sub_tree ->
  Hike_stack_model.sub_layout

(** One call-site binding (S16): the outgoing slot index, the storing
    def, and whether the FINAL store covers the whole cell (S21). *)
type site_binding = {
  sb_slot : int;
  sb_def : def term;
  sb_full : bool;
}

(** Stage A: the per-block store-to-call correspondence. *)
val stage_a :
  word:int ->
  abi:Hike_abi.t ->
  sp:var ->
  denote:(blk:blk term -> ?def:def term -> exp ->
          (Cbat_vsa.WordSet.t, Type.error) Result.t) ->
  sub term ->
  site_binding list Tid.Map.t

(** The rewrite driver: the promotion (Stage A2/C via the existing
    promote rewrite over the tree-derived facts) then Stage B's
    storage rewrite (Stack, Args, and Global) and the layout stamp. *)
val rewrite_program :
  word:int ->
  entry:int64 ->
  abi:Hike_abi.t ->
  sp:var ->
  symtab:Symtab.t option ->
  spans:data_span list ->
  denote:(blk:blk term -> ?def:def term -> exp ->
          (Cbat_vsa.WordSet.t, Type.error) Result.t) ->
  ctx:ctx ->
  program term ->
  program term

(** The spans served whole, as ONE component covering the span (the
    section's own image global is its storage): each row is the span's
    shared region id and bounds. *)
val whole_comps_of :
  word:int -> spans:data_span list -> ctx -> (int * int64 * int64) list

(** The emitter spec's Global components from the finalized data tree
    (S24): each CARVED range's word-grid tile and typed-width decision;
    whole-span ranges contribute nothing (their span serves whole). *)
val global_comps_of :
  word:int -> spans:data_span list -> ctx -> Hike_stack_model.sec_comp list
