(* Simon & King landmark widening: empty meets acquire landmarks; heads
   extrapolate toward them. *)

open Bap.Std

(* A recorded landmark; [dist] is the current distance, [dist_p] the
   previous measurement. *)
type lm_entry = {
  bound : Cbat_word.t;
  is_upper : bool;
  mutable dist : int option;
  mutable dist_p : int option;
}

(* The per-solve landmark table. *)
type t

(* One fresh table per solve. *)
val create : unit -> t

(* Drop entries of [h] and its SCC. *)
val clear_head : t -> Tid.t -> Tid.Set.t -> unit

(* Record an empty meet's disabled boundary at the enclosing head. *)
val observe_unsat_var :
  t -> var -> p:Cbat_clp_set_composite.t -> cstr:Cbat_clp_set_composite.t -> unit

(* Steps until the closest landmark; Zero needs another measurement, Inf
   widens. *)
val lm_calc_steps : t -> Tid.t -> [> `Zero | `Finite of int | `Inf ]

(* Commit current distances as previous. *)
val lm_advance : t -> Tid.t -> unit

(* Record a landmark for [head]. *)
val record_landmark_for_head :
  t -> head:Tid.t -> bound:Cbat_word.t -> is_upper:bool -> dist:int -> unit

(* Entries recorded for [head]. *)
val entries_for_head : t -> Tid.t -> lm_entry list

(* Extrapolate bounds toward landmarks; clamp at landmark and current
   bound. *)
val translate_to :
  steps:int -> Cbat_clp_set_composite.t -> Cbat_clp_set_composite.t ->
  lm_entry list -> Cbat_clp_set_composite.t

(* Run [f] with [head] widened; the previous head is restored. *)
val with_widening_head : t -> Tid.t option -> (unit -> 'a) -> 'a

(* The cell an entry is keyed by: the memory key's byte hull (each
   end as width/value) and stride — per-stride cells keep their own
   landmark rows. *)
module Cell_key : sig
  type t = {
    lo_width : int;
    lo_value : int64;
    hi_width : int;
    hi_value : int64;
    stride : int;
  }

  val equal : t -> t -> bool
end

(* Whether [h] carries only cell landmarks: the memory arm then runs the
   cells' own three-way. *)
val cell_driven : t -> Tid.t -> bool

(* Entries recorded for [h]'s [cell]. *)
val entries_for_cell : t -> Tid.t -> Cell_key.t -> lm_entry list

(* Record a landmark for [head]'s [cell]. *)
val record_landmark_for_cell :
  t ->
  head:Tid.t ->
  cell:Cell_key.t ->
  bound:Cbat_word.t ->
  is_upper:bool ->
  dist:int ->
  unit

(* Steps until the closest cell landmark; Zero needs another measurement,
   Inf widens. *)
val lm_calc_steps_for_cell :
  t -> Tid.t -> Cell_key.t -> [> `Zero | `Finite of int | `Inf ]

(* Commit a cell's current distances as previous. *)
val advance_cell : t -> Tid.t -> Cell_key.t -> unit

(* Drop a cell's entries. *)
val clear_cell : t -> Tid.t -> Cell_key.t -> unit

(* Record an empty meet's disabled boundary for a cell; [true] when one
   was recorded. *)
val observe_unsat_cell :
  t ->
  cell:Cell_key.t ->
  p:Cbat_clp_set_composite.t ->
  cstr:Cbat_clp_set_composite.t ->
  bool
