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
val compare_point : point -> point -> int
val equal_point : point -> point -> bool

val point : sec -> int64 -> point
val range : sec -> int64 -> int64 -> range

(** One membership fact: an access's occupied interval in one section,
    or an escape requirement ([m_def] absent, width 0).  [m_identity]
    marks bytes that need shared, un-carved storage. *)
type member = {
  m_sec : sec;
  m_lo : int64;
  m_hi : int64;
  m_sub : Tid.t;
  m_def : Tid.t option;
  m_width : int;
  m_store : bool;
  m_identity : bool;
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

(** The attribution snapshot: the collection's finalized trees, the raw
    member trees ownership closes, the def tags, each access def's
    projection, and the data spans served whole. *)
type ctx = {
  sub_trees : sub_tree Tid.Map.t;
  sub_members : member list Tree.t Tid.Map.t;
  data_tree : data_tree;
  tags : sec_tag Tid.Map.t;
  projections : projection option Tid.Map.t;
  conversions : conv Tid.Map.t;
  whole : data_span list;
}

(** The sub's storage spans: the layout's regions in the synth fact
    shape. *)
val spans_of_layout :
  synth:Hike_synth.table ref -> word:int -> Hike_stack_model.sub_layout ->
  Hike_synth.storage_span list

(** The end tree's storage decision: called once after ownership closes. *)
val finalize_tree :
  word:int -> entry:int64 -> whole:data_span list ->
  member list Tree.t -> sub_tree

(** The stack binding wholly owning [lo, hi]. *)
val binding_of_range : 'a Tree.t -> int64 -> int64 -> (range * 'a) option

(** Merge the hull of [ranges] into the tree; every intersecting binding
    is absorbed and keeps its members and extent. *)
val merge_ranges : member list Tree.t -> range list -> member list Tree.t

(** The def's memory access: (address, width in bytes, stores). *)
val access_of : def term -> (exp * int * bool) option

(** The def's storage conversion, read from its attribution projection
    and the finalized tree. *)
val conversion_of :
  word:int ->
  entry:int64 ->
  synth:Hike_synth.table ->
  tree:sub_tree ->
  data:data_tree ->
  projected:projection option ->
  access:(exp * int * bool) option ->
  conv * Tag.t option

(** The data binding wholly owning [c]: (component id, native low bound). *)
val owning_data_binding : data_tree -> int64 -> (int * int64) option

(** The word cell of a promotable Args member, when it names one. *)
val args_member_cell : word:int -> entry:int64 -> member -> int option

(** The storage's region id (the residue's id for non-carved storage). *)
val region_id_of_storage : storage -> int


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

(** The ownership query: the finalized binding owning [r]. *)
val storage_of_range : range_storage Tree.t -> range -> range_storage option

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
