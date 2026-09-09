open Core_kernel[@@warning "-D"]
open Option.Monad_infix

module Seq = Sequence

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

module Make(Interval : Interval) = struct
  type key = Interval.t [@@deriving sexp_of]

  module Point = Comparable.Make_plain(struct
      type t = Interval.point [@@deriving compare, sexp_of]
    end)

  type point = Interval.point [@@deriving compare, sexp_of]


  (* Trees are [node option]. *)
  type +'a node = {
    lhs : 'a node option;
    rhs : 'a node option;
    key : key;
    data : 'a;
    height : int;
    greatest : point;
    least : point;
  } [@@deriving fields, sexp_of]

  type +'a t = 'a node option [@@deriving sexp_of]

  let height = Option.value_map ~default:0 ~f:height

  let least = Option.map ~f:least
  let greatest = Option.map ~f:greatest

  let empty = None

  let bound f lhs top rhs = match lhs,rhs with
    | Some x, Some y -> f top (f x y)
    | Some x, None | None, Some x -> f top x
    | None, None -> top

  let create lhs key data rhs =
    let hl,hr = height lhs, height rhs in
    let mn = Interval.lower key in
    let mx = Interval.upper key in
    Some {
      lhs; rhs; key; data;
      height = (if hl >= hr then hl + 1 else hr + 1);
      least = bound Point.min (least lhs) mn (least rhs);
      greatest = bound Point.max (greatest lhs) mx (greatest rhs);
    }

  let singleton key data = create None key data None

  let rec min_binding = function
    | None -> None
    | Some {lhs=None; key; data} -> Some (key,data)
    | Some {lhs} -> min_binding lhs

  let bal l x d r =
    let hl,hr = height l, height r in
    if hl > hr + 2 then
      (* Left too heavy; rotation children exist. *)
      let t = Option.value_exn l in
      if height t.lhs >= height t.rhs then
        create t.lhs t.key t.data (create t.rhs x d r)
      else
        (* Inner child exists. *)
        let rhs = Option.value_exn t.rhs in
        create (create t.lhs t.key t.data rhs.lhs) rhs.key rhs.data
          (create rhs.rhs x d r)
    else if hr > hl + 2 then
      (* Right too heavy; rotation children exist. *)
      let t = Option.value_exn r in
      if height t.rhs >= height t.lhs then
        create (create l x d t.lhs) t.key t.data t.rhs
      else
        let lhs = Option.value_exn t.lhs in
        create (create l x d lhs.lhs) lhs.key lhs.data
          (create lhs.rhs t.key t.data t.rhs)
    else create l x d r

  let rec add map key data = match map with
    | None -> singleton key data
    | Some t ->
      let c = Interval.compare key t.key in
      if c = 0 then bal map key data None
      else if c < 0
      then bal (add t.lhs key data) t.key t.data t.rhs
      else bal t.lhs t.key t.data (add t.rhs key data)

  let is_dominated t r =
    let open Interval in
    Point.(lower r >= lower t.key && upper r <= upper t.key)

  let has_intersections t r =
    let open Interval in let open Point in
    let (p,q) = lower t.key, upper t.key
    and (x,y) = lower r, upper r in
    if p <= x
    then x <= q && p <= y
    else p <= y && x <= q

  let can't_be_in_tree t r =
    let open Interval in
    Point.(lower r > t.greatest || Point.(upper r < t.least))

  let can't_be_dominated t r =
    let open Interval in
    Point.(lower r < t.least || upper r > t.greatest)

  let query ~skip_if ~take_if start r =
    let open Sequence.Generator in
    let open Interval in
    let rec go = function
      | None -> return ()
      | Some t when skip_if t r -> return ()
      | Some t when take_if t r ->
        go t.lhs >>= fun () -> yield (t.key, t.data) >>= fun () -> go t.rhs
      | Some t -> go t.lhs >>= fun () -> go t.rhs in
    start |> go |> run

  let dominators m r = query m r
      ~skip_if:can't_be_dominated
      ~take_if:is_dominated

  let intersections m r = query m r
      ~skip_if:can't_be_in_tree
      ~take_if:has_intersections

  let dominates m r = not (Seq.is_empty (dominators m r))

  let rec remove_min_binding = function
    | None -> assert false
    | Some {lhs=None; rhs} -> rhs
    | Some t -> bal (remove_min_binding t.lhs) t.key t.data t.rhs

  let splice t1 t2 =
    match t1,t2 with
    | None, t | t, None -> t
    | _ -> match min_binding t2 with
      | None -> assert false
      | Some (key,data) -> bal t1 key data (remove_min_binding t2)

  (* Collect and remove intersections in one descent. *)
  let collect_remove_intersections map mem =
    let rec go = function
      | None -> (Seq.empty, None)
      | Some t when can't_be_in_tree t mem -> (Seq.empty, Some t)
      | Some t when has_intersections t mem ->
          let lseq, l = go t.lhs in
          let rseq, r = go t.rhs in
          (Seq.append (Seq.append lseq (Seq.singleton (t.key, t.data))) rseq,
           splice l r)
      | Some t ->
          let lseq, l = go t.lhs in
          let rseq, r = go t.rhs in
          (Seq.append lseq rseq, bal l t.key t.data r)
    in
    go map

  let filter_mapi map ~f =
    let rec fmap = function
      | None -> None
      | Some t -> match f t.key t.data with
        | None -> splice (fmap t.lhs) (fmap t.rhs)
        | Some data ->
          bal (fmap t.lhs) t.key data (fmap t.rhs) in
    fmap map

  let filter map ~f : _ t =
    filter_mapi map ~f:(fun _ x -> Option.some_if (f x) x)

  let to_sequence start =
    let open Seq.Generator in
    let rec go = function
      | None -> return ()
      | Some t ->
        go t.lhs >>= fun () -> yield (t.key, t.data) >>= fun () -> go t.rhs
    in
    start |> go |> run
end

module type Interval_binable = sig
  type t [@@deriving bin_io, compare, sexp]
  type point [@@deriving bin_io, compare, sexp]
  include Interval with type t := t and type point := point
end

module type S_binable = sig
  type 'a t [@@deriving bin_io, compare, sexp]
  include S with type 'a t := 'a t
end

module Make_binable(Interval : Interval_binable) = struct
  module Base = Make(Interval)

  type key = Interval.t [@@deriving sexp, compare, bin_io]

  type point = Interval.point [@@deriving compare, sexp, bin_io]

  type +'a node = 'a Base.node = {
    lhs : 'a node option;
    rhs : 'a node option;
    key : key;
    data : 'a;
    height : int;
    greatest : point;
    least : point;
  } [@@deriving fields, sexp, compare, bin_io]

  type +'a t = 'a node option [@@deriving sexp, compare, bin_io]

  include (Base : S with type key := key
                     and type point := point
                     and type 'a t := 'a t)

end
