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
val compare_point : point -> point -> int
val compare : range -> range -> int
val equal_point : point -> point -> bool
val equal : range -> range -> bool

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
    an Arg_slot a promoted incoming register. *)
type storage =
  | Stack_region of int
  | Stack_residue
  | Data_region of int
  | Arg_slot of int
[@@deriving equal, compare, sexp]

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
    unbounded form, the data-section anchoring, or Dead. *)
module Tag = Hike_stack_model.Tag

type sec_tag = Hike_stack_model.sec_tag

(** The completed attribution: the finalized trees and the def tags. *)
type ctx = {
  sub_trees : sub_tree Tid.Map.t;
  data_tree : data_tree;
  tags : sec_tag Tid.Map.t;
}

(** One projected portion of an access: the occupied interval in one
    space and its conversion eligibility there. *)
type portion = {
  pt_sec : sec;
  pt_lo : int64;
  pt_hi : int64;
  pt_elig : bool;
}
[@@deriving equal, compare, sexp]

(** Projects one address denotation of [width] bytes into its
    occupied-byte portions per represented space, plus the def's tag.
    Bottom yields no portion; an unknown address contributes its full
    possible range to each space it may touch. *)
val range_of_denotation :
  word:int ->
  entry:int64 ->
  spans:data_span list ->
  rip:bool ->
  width:int ->
  Cbat_vsa.WordSet.t ->
  sec_tag option * portion list

(** Collects the program's membership facts (memory accesses and
    escapes through the [denote] seam) and finalizes the ownership
    trees. *)
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

val access_of : def term -> (exp * int * bool) option
val is_rip_relative : def term -> bool
val is_const_chain : exp -> bool

(** The mem vars of storages carrying identity members — bytes another
    world reads through an escaped address; the DCE sweep keeps them
    as roots. *)
val escape_roots_of_tree : sub_tree -> Var.Set.t

(** The slim tag read off the def's value; [set_sec_tag] stamps it. *)
val sec_tag : def term -> sec_tag option
val set_sec_tag : sec_tag -> def term -> def term

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
val whole_comps_of :
  word:int -> spans:data_span list -> ctx -> (int * int64 * int64) list

(** The carved data ranges' global components (word-grid tile and
    typed width); whole spans contribute nothing. *)
val global_comps_of :
  word:int -> spans:data_span list -> ctx -> Hike_stack_model.sec_comp list
