(* Simon & King landmark widening: excluded boundaries are recorded at the
   enclosing cycle head; the head extrapolates toward them.  One table
   serves every key. *)

open Bap.Std

(* A recorded landmark; [dist] is the current distance, [dist_p] the
   previous measurement. *)
type lm_entry = {
  bound : Cbat_word.t;
  is_upper : bool;
  mutable dist : int option;
  mutable dist_p : int option;
}

(* The cell a landmark is about: the memory key's byte hull (each end as
   width/value) and stride — per-stride cells keep their own rows. *)
type cell_desc = {
  origin : Hike_origin.t;
  lo_width : int;
  lo_value : int64;
  hi_width : int;
  hi_value : int64;
  stride : int;
}

(* What a landmark is about: a word at the head, or a memory cell at the
   head.  The head is the table's outer key. *)
type key = Word | Cell of cell_desc

(* The per-solve landmark table. *)
type t

(* One fresh table per solve. *)
val create : unit -> t

(* Drop the rows of [h] and its SCC. *)
val clear_head : t -> Tid.t -> Tid.Set.t -> unit

(* Record an excluded behavior's boundary at the enclosing head; [true]
   when a landmark was recorded. *)
val observe_unsat :
  t -> key:key -> p:Cbat_clp_set_composite.t -> cstr:Cbat_clp_set_composite.t ->
  bool

(* Entries recorded for [key] at [head]. *)
val entries : t -> Tid.t -> key -> lm_entry list

(* Every key recorded at [head], oldest row first. *)
val keys_at : t -> Tid.t -> key list

(* Steps until the closest landmark; Zero needs another measurement, Inf
   widens. *)
val steps : t -> Tid.t -> key -> [> `Zero | `Finite of int | `Inf ]

(* Record a landmark for [key] at [head]. *)
val record :
  t ->
  head:Tid.t ->
  key:key ->
  bound:Cbat_word.t ->
  is_upper:bool ->
  dist:int ->
  unit

(* Commit [key]'s current distances as previous. *)
val advance : t -> Tid.t -> key -> unit

(* Commit every key recorded at [head]. *)
val advance_head : t -> Tid.t -> unit

(* Drop [key]'s entries. *)
val clear_key : t -> Tid.t -> key -> unit

(* Whether [h] carries cell landmarks and no word landmark: the memory arm
   then runs the cells' own three-way. *)
val cell_driven : t -> Tid.t -> bool

(* Extrapolate bounds toward landmarks; clamp at landmark and current
   bound. *)
val translate_to :
  steps:int -> Cbat_clp_set_composite.t -> Cbat_clp_set_composite.t ->
  lm_entry list -> Cbat_clp_set_composite.t

(* Run [f] with [head] widened; the previous head is restored. *)
val with_widening_head : t -> Tid.t option -> (unit -> 'a) -> 'a
