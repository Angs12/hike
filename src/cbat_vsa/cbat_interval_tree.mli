(* Interval tree over [Interval] keys: the surface [cbat_ai_memmap]'s Mem
   uses (add / query / filter). *)

open Core_kernel[@@warning "-D"]

module type Interval = sig
  type t [@@deriving compare, sexp_of]
  type point [@@deriving compare, sexp_of]
  val lower : t -> point
  val upper : t -> point
end


module type S = sig
  type 'a t [@@deriving sexp_of]
  type key
  type point

  val empty : 'a t
  val add : 'a t -> key -> 'a -> 'a t
  val dominators : 'a t -> key -> (key * 'a) Sequence.t
  val intersections : 'a t -> key -> (key * 'a) Sequence.t
  val collect_remove_intersections
    :  'a t -> key -> (key * 'a) Sequence.t * 'a t
  val dominates : 'a t -> key -> bool
  val filter : 'a t -> f:('a -> bool) -> 'a t
  val to_sequence : 'a t -> (key * 'a) Sequence.t
end

module Make(Interval : Interval) : S
  with type key := Interval.t
   and type point := Interval.point

module type Interval_binable = sig
  type t [@@deriving bin_io, compare, sexp]
  type point [@@deriving bin_io, compare, sexp]
  include Interval with type t := t and type point := point
end

module type S_binable = sig
  type 'a t [@@deriving bin_io, compare, sexp]
  include S with type 'a t := 'a t
end

module Make_binable(Interval : Interval_binable) : S_binable
  with type key := Interval.t
   and type point := Interval.point
