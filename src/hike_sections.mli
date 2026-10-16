(* The ownership pass: [range_of_denotation] projects an address
   denotation into occupied-byte portions, collection builds the two
   interval trees, finalization decides each merged range's storage. *)

open Bap.Std

(** The represented sections, in declaration order. *)
type sec = Hike_stack_model.sec [@@deriving equal, compare, sexp]

(** One data section's inclusive native byte span and its
    copy-relocated slot addresses (externally-owned bytes). *)
type data_span = {
  ds_sec : sec;
  ds_lo : int64;
  ds_hi : int64;
  ds_slots : int64 list;
}
[@@deriving equal, compare, sexp]

(** A point of the section-ordered line: the section plus its local
    position. *)
type point = { p_sec : sec; p_pos : int64 } [@@deriving sexp]

(** An inclusive occupied-byte range. *)
type range = { lo : point; hi : point } [@@deriving sexp]

(** The endpoint ordering: section first, then the section's numeric
    order (signed for Stack/Args, unsigned for data sections). *)
val compare : range -> range -> int
val equal : range -> range -> bool

val point : sec -> int64 -> point
val range : sec -> int64 -> int64 -> range

(** One membership fact: an access's occupied interval in one section,
    or an escape requirement ([m_def] absent, width 0).  [m_identity]
    marks bytes that need shared, un-carved storage.  [m_callwin] marks
    the extent a calling block exposes to its callee: it forces the
    residue (the window shadow's storage) but is not an escape — the
    callee reads the outgoing cells through the typed slot pointers. *)
type member = {
  m_sec : sec;
  m_lo : int64;
  m_hi : int64;
  m_sub : Tid.t;
  m_def : Tid.t option;
  m_width : int;
  m_store : bool;
  m_identity : bool;
  m_callwin : bool;
}
[@@deriving equal, compare, sexp]

(** The finalized storage of one merged range: a stack region id keys
    a per-sub alloca (the residue, id 0, is the fallback), a data
    region id a module-wide global (a whole span is one data region),
    an Arg_slot the caller's argument cells (the slot index is the
    access's own word cell). *)
type storage =
  | Stack_region of int
  | Stack_residue
  | Data_region of int
  | Arg_slot

(** One finalized binding: the storage decision and its members
    (newest first). *)
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

(** The slim def-carried classification: the def's section with its
    ADDRESS bounds (not the occupied-byte bounds), the justified
    unbounded form, or the data-section anchoring. *)
module Tag = Hike_stack_model.Tag

type sec_tag = Hike_stack_model.sec_tag

(** One projected portion of an access: the occupied interval in one
    space and its conversion eligibility there. *)
type portion = {
  pt_sec : sec;
  pt_lo : int64;
  pt_hi : int64;
  pt_elig : bool;
}
[@@deriving equal, compare, sexp]

(** The def's projection: the reduced tag, the address denotation's
    runtime origin (the analysis's own fact — the rewrite consumes it;
    no band re-derivation), and the portions. *)
type projection = {
  tag : sec_tag option;
  origin : Hike_origin.t option;
  portions : portion list;
  (** The access's stack-offset hull, when the denotation names one. *)
  offsets : (int64 * int64) option;
}

type conv = Hike_synth_addr.conv =
  | Conv_region of int                    (* the region id *)
  | Conv_window                           (* the incoming window: the caller's world *)
  | Conv_slot of int * int                (* slot index, intra-slot byte *)
  | Conv_global of int                    (* the component id *)
  | Keep

(** The completed attribution: the finalized trees, the def tags, each
    access def's projection, and the data spans served whole. *)
type ctx = {
  sub_trees : sub_tree Tid.Map.t;
  data_tree : data_tree;
  tags : sec_tag Tid.Map.t;
  projections : projection option Tid.Map.t;
  conversions : conv Tid.Map.t;
  whole : data_span list;
}

(** One def's rewrite facts: the access's conversion (the mem
    re-point) plus the storage-relative address forms — a value def's
    whole rhs, an access def's mem-node address. *)
type def_fact = {
  fr_conv : conv;
  fr_bits : int;
  fr_addr : exp option;
  fr_rhs : exp option;
}

(** The sub's storage spans: the layout's regions in the synth fact
    shape. *)
val spans_of_layout :
  word:int -> Hike_stack_model.sub_layout -> Hike_synth.storage_span list

(** Every def's rewrite facts, selected from the finalized trees, the
    access conversions, the storage spans and the value's leaves. *)
val def_facts :
  word:int -> entry:int64 -> abi:Hike_abi.t ->
  tree:sub_tree -> data:data_tree ->
  projections:projection option Tid.Map.t ->
  conversions:conv Tid.Map.t ->
  storages:Hike_synth.storage_span list ->
  window_param:bool -> vla_tids:Tid.Set.t -> spans:data_span list ->
  denote:(blk:blk term -> ?def:def term -> exp ->
          (Cbat_vsa.WordSet.t, Type.error) Result.t) ->
  is_dyn_alloc:(def term -> bool) ->
  sub term -> def_fact Tid.Map.t


(** Projects one address denotation of [width] bytes into its
    occupied-byte portions per represented space, plus the def's tag.
    Bottom yields no portion; an unknown address contributes its full
    possible range to each space it may touch. *)
val range_of_denotation :
  word:int ->
  entry:int64 ->
  spans:data_span list ->
  synth:Hike_synth.table ->
  address:exp ->
  width:int ->
  Cbat_vsa.WordSet.t ->
  sec_tag option * portion list

(** Why an address denotated TOP: the denotation query itself failed, a
    stack-symbolic set with no surviving bounds, or a plain top (no
    stack or section basis — the heap). *)
type top_cause = Query_failed | Unbounded_stack | Foreign

(** The full-span claim for a TOP address: a stack-symbolic top clamps
    below the entry; any other top claims the whole sub-local line.
    Every full-span member is identity, never carved. *)
val top_claim :
  cause:top_cause -> entry:int64 -> word:int -> sec_tag option * portion list

(** Collects the program's membership facts (memory accesses and
    escapes through the [denote] seam) and finalizes the ownership
    trees. *)
val attribute :
  facts:Hike_kb.facts ->
  word:int ->
  entry:int64 ->
  spans:data_span list ->
  program term ->
  ctx

(** The sub's dynamic allocations: the seed's confirmed frames, keyed by
    the def computing each base. *)
val dynamic_allocs_of :
  facts:Hike_kb.facts -> sub term -> Hike_def_slots.dyn_alloc Tid.Map.t

(** The ownership query: the finalized binding owning [r]. *)
val storage_of_range : range_storage Tree.t -> range -> range_storage option

(** The section space predicates: data sections vs the sub-local
    stack/arg spaces. *)
(** The def's memory access: (address, width in bytes, stores?). *)
(** The mem vars of storages whose bytes escape this sub: a storage
    carrying an escape extent (a stored stack-symbolic value, an
    incoming stack-address parameter), one a typed call argument
    names — a promoted [hike_argN] binding the callee's slot convention
    reaches, or an argument register holding a rewritten storage-base
    address — or the residue shadow a model-window callee reads (a
    variadic callee's overflow cells, an unpromotable Args claim).  The
    DCE sweep keeps the rooted storages' defs. *)
val escape_roots_of_sub :
  addr_bits:int ->
  abi:Hike_abi.t ->
  arities:int Tid.Map.t ->
  window_readers:Tid.Set.t ->
  tree:sub_tree ->
  sub term ->
  Var.Set.t

(** Stamps the ctx's slim tags onto the sub's defs (a term mapper). *)
val stamp_tags : ctx -> sub term -> sub term

(** The sub's layout from its finalized tree: the region components'
    geometry and the fallback frame. *)
val layout_of_tree :
  word:int ->
  entry:int64 ->
  abi:Hike_abi.t ->
  sub:sub term ->
  sub_tree ->
  Hike_stack_model.sub_layout

(** Each whole-served span as one row: its shared region id and
    bounds (the section's own image global is the storage). *)
val whole_comps_of : ctx -> (int * int64 * int64) list

(** The carved data ranges' global components (word-grid tile and
    typed width); whole spans contribute nothing. *)
val global_comps_of :
  word:int -> spans:data_span list -> ctx -> Hike_stack_model.sec_comp list

(** The section metadata rows, in the fixed table order; the spans,
    emitter spec, and copy-reloc slots all project from this builder. *)
type sec_meta = {
  sm_type : sec;
  sm_access : Hike_section.access;
  sm_lo : int64;
  sm_hi : int64;
  sm_words : int;
  sm_image : Bytes.t option;  (* None = the bss region *)
  sm_copy_relocs : (int * string) list;  (* bss: (byte offset, symbol) *)
}

(** The ELF section table rows ([None] = absent from the binary). *)
val sec_meta : word:int -> Project.t -> sec_meta option list

(** The attribution's data spans: each reserved section's bounds and
    copy-relocated slot addresses, in the fixed table order. *)
val attrib_spans : meta:sec_meta option list -> data_span list

(** The emitter's section spec; a [whole] entry (id, lo, hi) is a span
    served whole — the section's own image global is the id's storage.
    [relative]/[externals] are the loader's relocation facts the
    initializer consults; the spec also carries the absolute
    copy-relocation slot addresses. *)
val section_spec_of :
  word:int ->
  comps:Hike_stack_model.sec_comp list ->
  whole:(int * int64 * int64) list ->
  meta:sec_meta option list ->
  tls:Bil2llvm_env.tls_spec option ->
  relative:(int64 * int64) list ->
  externals:(int64 * string) list -> Bil2llvm_env.section_spec

(** The promoted slot count of a finalized tree: the highest
    Arg_slot cell index + 1; 0 when the tree names none. *)
val slot_arity : word:int -> entry:int64 -> sub_tree -> int
