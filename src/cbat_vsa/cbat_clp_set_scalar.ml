(* ************************************************************************* *)
(*  *)
(* Copyright (C) Draper Laboratory. Licensed under project LICENSE. *)
(*  *)
(* This file is provided under the license found in the LICENSE file in *)
(* the top-level directory of this project. *)
(*  *)
(* This work is funded in part by the ONR/NAWC Contract N6833518C0107. Its *)
(* content does not necessarily reflect the position or policy of the US *)
(* Government and no official endorsement should be inferred. *)
(*  *)
(* ************************************************************************* *)

open !Core
open Bap.Std

module Word_ops = Cbat_word
module Utils = Cbat_vsa_utils
module Clp = Cbat_clp
module P = Clp.Pieces
module FinSet = Cbat_fin_set
module Origin = Hike_origin

type clp = Clp.t
type word = Cbat_word.t
type fset = FinSet.t

(* Large sets are one Clp piece union; small ones FinSets; relative
   addresses carry their origin: [Rel (o, offs)] = [o]'s base plus the
   exact offset piece union [offs], one origin per value.  A value is
   ONE of those (the common case — no list cell), or [Many] of the
   canonical multi-piece list ([Many] never nests: [canonical]
   flattens; a mixed-origin pool materialises to [Abs]).
   Extrema answer from the offsets; shape-losing ops degrade to that
   plain hull; ops keeping unknown base bits answer top — the base is
   a tag except its certified low bits. *)
type t =
  | Clp of P.t
  | FinSet of FinSet.t
  | Many of t list
  | Rel of Origin.t * P.t
[@@deriving bin_io, sexp, compare]
type idx = int

(* Base 2^62 + 8: the +8 is the ABI entry residue — a call-entered
   RSP is 8 (mod 16). *)
let stack_base = (Origin.facts Origin.Stack).base
(* The symbolic stack segment spans 8 MiB above the base — a TOP
   stack claim covers at most [stack_span] bytes. *)
let stack_span = Origin.stack_span

let w64_of_i64 (i : int64) : Cbat_word.t =
  Cbat_word.of_word (Word.of_int64 ~width:64 i)

(* ---------------- leaf views (total over [Many]) ---------------- *)

let rec bitwidth (t : t) : int =
  match t with
  | Rel (_, _) -> 64
  | Clp ps -> P.bitwidth ps
  | FinSet s -> FinSet.bitwidth s
  | Many ps -> List.fold ps ~init:0 ~f:(fun a q -> Stdlib.max a (bitwidth q))

let rec is_bottom (t : t) : bool =
  match t with
  | Clp ps | Rel (_, ps) -> P.is_bottom ps
  | FinSet s -> Cbat_word.is_zero (FinSet.cardinality s)
  | Many ps -> List.for_all ps ~f:is_bottom

(* |segment| * |offs| at width 65.  The product SATURATES: a wrapped
   product would under-report. *)
let stack_cardinality (offs : P.t) : word =
  let width = 65 in
  let a = Cbat_word.of_int ~width (Stdlib.Int64.to_int stack_span + 1) in
  let b = Cbat_word.cap_at_width ~width (P.cardinality offs) in
  if Cbat_word.is_zero a || Cbat_word.is_zero b then
    Cbat_word.zero width
  else if Cbat_word.is_one a then b
  else if Cbat_word.is_one b then a
  else
    (* a = 2^23 + 1, so [b <= 2^39] keeps the exact product below
       2^63; anything larger saturates. *)
    if Cbat_word.leq_int b 0x8000000000 then Cbat_word.mul a b
    else Cbat_word.ones width

(* The single-progression hull of a piece union. *)
let hull_of_pieces (ps : P.t) : clp option =
  match P.to_list ps with
  | [] -> None
  | p :: rest -> Some (List.fold rest ~init:p ~f:Clp.union)

let pieces_of_words ~width (l : word list) : P.t = P.of_list ~width l

let pieces_of_finset (s : fset) : P.t =
  pieces_of_words ~width:(FinSet.bitwidth s) (FinSet.iter s)

let clp_of_finset fs : clp =
  let width = FinSet.bitwidth fs in
  match FinSet.iter fs with
  | [] -> Clp.bottom width
  | [ x ] -> Clp.singleton x
  | l -> Clp.of_list ~width l

(* ---------------- constructors ---------------- *)

let stack_word (offs : Clp.t) : t = Rel (Origin.Stack, P.of_progression offs)

let stack_word_i64 (k : int64) : t =
  Rel (Origin.Stack, P.singleton (w64_of_i64 k))

(* A module address: its link-time word in its section; an address
   outside every section stays a plain word. *)
let module_address (a : int64) : t =
  match Origin.Regions.of_address a with
  | Some r -> Rel (Origin.Rip r, P.singleton (w64_of_i64 a))
  | None -> FinSet (FinSet.singleton (w64_of_i64 a))

(* A fresh VLA frame: offset 0 is the allocation base (the post-move SP). *)
let vla_frame (tid : Tid.t) : t =
  Rel (Origin.Vla tid, P.singleton (w64_of_i64 0L))

(* a + b + c with int64 overflow check. *)
let checked_add3 (a : int64) (b : int64) (c : int64) : int64 option =
  let pos x = Stdlib.Int64.compare x 0L >= 0 in
  let ab = Stdlib.Int64.add a b in
  if Bool.equal (pos a) (pos b) && not (Bool.equal (pos ab) (pos a)) then None
  else
    let abc = Stdlib.Int64.add ab c in
    if Bool.equal (pos ab) (pos c) && not (Bool.equal (pos abc) (pos ab))
    then None
    else Some abc

(* The allocation base's entry-line (segment-relative) range, known only
   when the SP-before and the size bound it. *)
let vla_base_range (tid : Tid.t) : (int64 * int64) option =
  match Origin.Vla_seed.extent tid with
  | Some { Origin.base_lo = Some lo; base_hi = Some hi; _ } -> Some (lo, hi)
  | _ -> None

(* Only a bounded singleton allocation base supplies a fixed residue. *)
let base_facts (o : Origin.t) : Origin.facts =
  match o with
  | Origin.Vla tid ->
    (match vla_base_range tid with
     | Some (lo, hi) when Int64.equal lo hi ->
       { (Origin.facts Origin.Stack) with base = Stdlib.Int64.add stack_base lo }
     | _ -> Origin.facts o)
  | _ -> Origin.facts o

(* Origins whose offsets are absolute words: plain values and module
   addresses, whose anchor records provenance, not an unknown base. *)
let absolute_line (o : Origin.t) : bool =
  match o with
  | Origin.Abs | Origin.Rip _ -> true
  | Origin.Stack | Origin.Window | Origin.Vla _ -> false

(* The exact hull [base + offs_lo, base + offs_hi]; a missing
   direction clamps to the origin's materialisation bound — a
   relative claim stays in its origin's extent.  A VLA value is
   frame-relative: its base is the allocation's, and an unknown base has
   no entry-line position (top). *)
let plain_bounds (o : Origin.t) (offs : P.t) : (int64 * int64) option =
  let k_int w = match Cbat_word.to_int64 w with Ok v -> Some v | Error _ -> None in
  match o with
  | Origin.Vla tid -> (
    match vla_base_range tid with
    | Some (blo, bhi) -> (
      match Option.bind (P.min_elem offs) ~f:k_int,
            Option.bind (P.max_elem offs) ~f:k_int with
      | Some klo, Some khi -> (
        match checked_add3 stack_base blo klo, checked_add3 stack_base bhi khi with
        | Some lo, Some hi when Stdlib.Int64.compare hi lo >= 0 -> Some (lo, hi)
        | _ -> None)
      | _ -> None)
    | None -> None)
  | _ ->
    let f = Origin.facts o in
    let floor = Stdlib.Int64.add f.Origin.base f.Origin.lo in
    let ceil = Stdlib.Int64.add f.Origin.base f.Origin.hi in
    let side = function
      | Some w ->
        (match Cbat_word.to_int64 w with
         | Ok v -> checked_add3 f.Origin.base 0L v
         | Error _ -> None)
      | None -> None
    in
    let lo = match P.min_elem offs with
      | Some w -> side (Some w)
      | None -> Some floor in
    let hi = match P.max_elem offs with
      | Some w -> side (Some w)
      | None -> Some ceil in
    match lo, hi with
    | Some lo, Some hi when Stdlib.Int64.compare hi lo >= 0 -> Some (lo, hi)
    | _ -> None

(* A relative value's plain twin: the exact hull as a step-1 piece. *)
let rec to_plain (t : t) : t =
  match t with
  | Rel (o, offs) when absolute_line o -> Clp offs
  | Rel (o, offs) ->
    (match plain_bounds o offs with
     | Some (cmin, cmax)
       when Stdlib.Int64.compare cmin 0L >= 0
            && Stdlib.Int64.compare cmax cmin >= 0 ->
       Clp (P.of_progression
              (Clp.interval ~width:64 (w64_of_i64 cmin) (w64_of_i64 cmax)))
     | _ -> Clp (P.top 64))
  | Many ps ->
    (match canonical (List.map ps ~f:to_plain) with
     | Clp _ | FinSet _ | Rel _ as q -> q
     | Many ps' -> Many ps')
  | Clp _ | FinSet _ -> t

(* ---------------- canonicalization ---------------- *)

(* The canonical value: one leaf, or [Many] of the canonical leaf list
   in the fixed order Clp, FinSet, Rel (no nesting); bottoms drop
   (an all-bottom value keeps one empty FinSet so the width survives);
   an over-budget FinSet pool promotes to its exact piece runs; a lone
   small plain piece union keeps its exact FinSet twin (the tier).
   The relative pool groups by origin: a pool of two or more origins
   is not a value — its members materialise into the plain pool. *)
and canonical (ps : t list) : t =
  let alive = List.filter ps ~f:(fun q -> not (is_bottom q)) in
  let rels =
    List.filter_map ps ~f:(function Rel (o, x) -> Some (o, x) | _ -> None)
  in
  let rel_origins =
    List.fold rels ~init:[] ~f:(fun acc (o, _) ->
        if List.exists acc ~f:(Origin.equal o) then acc else acc @ [ o ])
  in
  let so_pool, mixed_pool =
    match rel_origins with
    | [] -> (None, [])
    | [ o ] ->
      let offs =
        List.filter_map rels
          ~f:(fun (o', x) -> if Origin.equal o' o then Some x else None)
      in
      (match offs with
       | [] -> (None, [])
       | x :: rest -> (Some (o, List.fold rest ~init:x ~f:P.union), []))
    | _ ->
      ( None,
        List.filter_map rels ~f:(fun (o, x) ->
            match to_plain (Rel (o, x)) with
            | Clp p -> Some p
            | _ -> None) )
  in
  (match alive, so_pool with
  | [], Some (o, offs) ->
    (* The symbolic bottom keeps its origin: an empty offset set is
       still a relative value (its consumers span the full key line). *)
    Rel (o, offs)
  | [], None ->
    (match ps with
     | [] -> FinSet (FinSet.bottom 1)
     | _ ->
       let w =
         List.fold ps ~init:1 ~f:(fun a q -> Stdlib.max a (bitwidth q)) in
       FinSet (FinSet.bottom w))
  | _ ->
    let clps =
      List.append mixed_pool
        (List.filter_map ps ~f:(function Clp x -> Some x | _ -> None))
    in
    let fss =
      List.filter_map ps ~f:(function FinSet x -> Some x | _ -> None) in
    let fs_total =
      List.fold fss ~init:0 ~f:(fun a s ->
          a
          + (match Cbat_word.to_int (FinSet.cardinality s) with
             | Ok n -> n
             | Error _ -> Stdlib.max_int))
    in
    let promote = fs_total > Utils.fin_set_size in
    let clp_sources =
      List.append clps
        (if promote then List.map fss ~f:pieces_of_finset else [])
    in
    (* A pool of mixed widths has no progression union: it is top at
       the widest (sound; extract/cast over a Many produce leaves of
       the op's own width). *)
    let clp_piece =
      match clp_sources with
      | [] -> None
      | x :: rest ->
        let w = P.bitwidth x in
        if List.for_all rest ~f:(fun q -> Stdlib.Int.equal (P.bitwidth q) w)
        then Some (List.fold rest ~init:x ~f:P.union)
        else Some (P.top (List.fold rest ~init:w ~f:(fun a q -> Stdlib.max a (P.bitwidth q))))
    in
    let fs_piece =
      if promote then None
      else
        match fss with
        | [] -> None
        | x :: rest -> Some (List.fold rest ~init:x ~f:FinSet.union)
    in
    (* Contained pieces drop: a FinSet leaf covered by the Clp leaf adds
       no element, and a Clp leaf covered by the FinSet is that FinSet.
       Both would double-count the overlap in [cardinality]. *)
    let clp_piece, fs_piece =
      match clp_piece, fs_piece with
      | Some cps, Some fss
        when List.for_all (FinSet.iter fss) ~f:(fun w -> P.elem w cps) ->
        (Some cps, None)
      | Some cps, Some fss
        when (not (P.is_top cps))
             && not (Cbat_word.gt_int (P.cardinality cps) Utils.fin_set_size)
             && List.for_all (P.elements cps) ~f:(fun w -> FinSet.elem w fss)
        -> (None, Some fss)
      | c, f -> c, f
    in
    let clp_piece, fs_piece =
      match clp_piece, fs_piece with
      | Some cps, None
        when (not (P.is_bottom cps)) && not (P.is_top cps)
             && not (Cbat_word.gt_int (P.cardinality cps) Utils.fin_set_size)
        -> None, Some (FinSet.of_list ~width:(P.bitwidth cps) (P.elements cps))
      | c, f -> c, f
    in
    (* A bottom relative pool drops against live plain pieces. *)
    let so_piece =
      match so_pool with
      | Some (o, offs) when not (P.is_bottom offs) -> Some (o, offs)
      | _ -> None
    in
    let leaves =
      List.filter_map
        [ Option.map clp_piece ~f:(fun x -> Clp x);
          Option.map fs_piece ~f:(fun x -> FinSet x);
          Option.map so_piece ~f:(fun x -> Rel (fst x, snd x)) ]
        ~f:(fun q -> q)
    in
    (match leaves with
     | [ q ] -> q
     | [] ->
       (* No leaf survived: a bottom at the widest input, never an empty
          [Many] (which would carry width 0). *)
       FinSet
         (FinSet.bottom
            (List.fold ps ~init:1 ~f:(fun a q -> Stdlib.max a (bitwidth q))))
     | ps -> Many ps))


(* The plain twin: a symbolic piece materialized, a plain value as-is. *)
let plain_view (t : t) : t = match t with Rel _ -> to_plain t | q -> q

(* The value's runtime origin: [Some o] exactly when every piece of the
   value is relative to the one origin [o]; absolute, plain, and
   mixed-origin values are [None]. *)
let rec origin (t : t) : Origin.t option =
  match t with
  | Rel (o, _) -> Some o
  | Clp _ | FinSet _ -> None
  | Many ps ->
    (match List.map ps ~f:origin with
     | (Some o) :: rest ->
       if
         List.for_all rest
           ~f:(function Some o' -> Origin.equal o o' | None -> false)
       then Some o
       else None
     | _ -> None)

(* Re-tags a relative value's origin, offsets unchanged — the VLA
   seed's framing step (the entry-line positions ARE the new frame's). *)
let set_origin (o : Origin.t) (t : t) : t =
  match t with Rel (_, offs) -> Rel (o, offs) | q -> q

(* Plain-operand top test. *)
let rec plain_is_top (t : t) : bool =
  match t with
  | Clp ps -> P.is_top ps
  | FinSet _ -> false
  | Rel (_, offs) -> P.is_top offs
  | Many ps -> List.exists ps ~f:plain_is_top

(* The plain single-progression hull of the whole value. *)
let as_clp (t : t) : clp =
  match to_plain t with
  | Clp ps ->
    (match hull_of_pieces ps with
     | Some p -> p
     | None -> Clp.top (Stdlib.max 1 (P.bitwidth ps)))
  | FinSet s -> clp_of_finset s
  | Many ps ->
    let hulls =
      List.filter_map ps ~f:(function
        | FinSet s -> Some (clp_of_finset s)
        | Clp hps -> hull_of_pieces hps
        | Rel _ -> None
        | Many _ -> None)
    in
    (match hulls with
     | [] -> Clp.top 64
     | p :: rest -> List.fold rest ~init:p ~f:Clp.union)
  | _ -> Clp.top 64

let of_list ~width l : t =
  canonical
    [ (if List.length l > Utils.fin_set_size then Clp (P.of_list ~width l)
       else FinSet (FinSet.of_list ~width l)) ]

let singleton w : t = FinSet (FinSet.singleton w)

let of_clp (p : clp) : t = canonical [ Clp (P.of_progression p) ]

let bottom i = FinSet (FinSet.bottom i)
let top i = canonical [ Clp (P.top i) ]

(* One leaf, or the [Many] pieces. *)
let leaves (t : t) : t list = match t with Many ps -> ps | q -> [ q ]

(* The pairwise leaf fan-out: [f] per leaf pair, canonically merged. *)
let pairwise (f : t -> t -> t list) (t1 : t) (t2 : t) : t =
  canonical
    (List.concat_map (leaves t1) ~f:(fun q1 ->
         List.concat_map (leaves t2) ~f:(fun q2 -> f q1 q2)))

(* ---------------- the kind-aligned leaf pairing ---------------- *)

(* The leaf of each kind: a canonical value carries at most one (the
   [canonical] fold collapses same-kind leaves), so the first match is
   the only one. *)
let clp_leaf (t : t) : P.t option =
  match t with
  | Clp ps -> Some ps
  | Many ps -> List.find_map ps ~f:(function Clp x -> Some x | _ -> None)
  | FinSet _ | Rel _ -> None

let fs_leaf (t : t) : fset option =
  match t with
  | FinSet s -> Some s
  | Many ps -> List.find_map ps ~f:(function FinSet x -> Some x | _ -> None)
  | Clp _ | Rel _ -> None

let rel_leaf (t : t) : (Origin.t * P.t) option =
  match t with
  | Rel (o, x) -> Some (o, x)
  | Many ps ->
    List.find_map ps ~f:(function Rel (o, x) -> Some (o, x) | _ -> None)
  | Clp _ | FinSet _ -> None

(* The join pairing: every kind carried by EITHER side contributes — a
   shared kind takes its own join, a one-sided kind is carried (the join
   includes it).  Exact for the lattice join, which is why the join may
   carry where a widening may not. *)
let pair_join ~(clp_op : P.t -> P.t -> P.t) ~(fs_op : fset -> fset -> fset)
    ~(rel_op : Origin.t -> P.t -> Origin.t -> P.t -> t) (t1 : t) (t2 : t) : t =
  let parts =
    (match clp_leaf t1, clp_leaf t2 with
     | Some a, Some b -> [ Clp (clp_op a b) ]
     | Some a, None | None, Some a -> [ Clp a ]
     | None, None -> [])
    @ (match fs_leaf t1, fs_leaf t2 with
       | Some a, Some b -> [ FinSet (fs_op a b) ]
       | Some a, None | None, Some a -> [ FinSet a ]
       | None, None -> [])
    @ (match rel_leaf t1, rel_leaf t2 with
       | Some (o1, a), Some (o2, b) -> [ rel_op o1 a o2 b ]
       | Some (o, a), None | None, Some (o, a) -> [ Rel (o, a) ]
       | None, None -> [])
  in
  canonical parts

(* The concrete extrema of a set, before any stack projection. *)
let extrema (t : t) : (Cbat_word.t * Cbat_word.t) option =
  let leaf (q : t) : (Cbat_word.t * Cbat_word.t) option =
    let pair lo hi = Option.map2 lo hi ~f:(fun lo hi -> (lo, hi)) in
    match q with
    | Rel (o, offs) ->
      (match plain_bounds o offs with
       | Some (cmin, cmax) -> Some (w64_of_i64 cmin, w64_of_i64 cmax)
       | None -> None)
    | Clp ps -> pair (P.min_elem ps) (P.max_elem ps)
    | FinSet s -> pair (FinSet.min_elem s) (FinSet.max_elem s)
    | Many _ -> None
  in
  let rec go acc (t : t) =
    match t with
    | Many ps -> List.fold ps ~init:acc ~f:go
    | q ->
      (match leaf q, acc with
       | None, acc -> acc
       | Some (lo, hi), None -> Some (lo, hi)
       | Some (lo, hi), Some (alo, ahi) ->
         Some
           ((if Cbat_word.compare lo alo < 0 then lo else alo),
            (if Cbat_word.compare hi ahi > 0 then hi else ahi)))
  in
  go None t

(* Stack identity comes only from the carried runtime origin. *)
let in_stack_segment (t : t) : bool =
  Option.exists (origin t) ~f:Origin.names_stack_line

(* The offsets' SIGNED extrema of a stack value (the offset line is
   signed: negative below the entry).  Exact over the arcs of every
   progression — a wrapped SP piece measures instead of failing. *)
let offsets_signed_extrema (offs : P.t)
    : (Cbat_word.t * Cbat_word.t) option =
  let fold (acc : (Cbat_word.t * Cbat_word.t) option)
      (p : Clp.t) : (Cbat_word.t * Cbat_word.t) option =
    match Clp.min_elem_signed p, Clp.max_elem_signed p with
    | Some lo, Some hi ->
      (match acc with
       | None -> Some (lo, hi)
       | Some (alo, ahi) ->
         Some
           ((if Cbat_word.compare (Cbat_word.signed lo) (Cbat_word.signed alo)
                < 0 then lo else alo),
            (if Cbat_word.compare (Cbat_word.signed hi) (Cbat_word.signed ahi)
                > 0 then hi else ahi)))
    | _ -> acc
  in
  List.fold (P.to_list offs) ~init:None ~f:fold

(* The solve-boundary refinement: a wholly window-side relative value
   (every offset at/above the ABI word) names the caller's frame
   origin.  A VLA frame keeps its origin; the routing gate refuses an
   out-of-frame offset at the stamp, not here. *)
let refine_origin ~(word : int) (t : t) : t =
  let extrema_i64 offs =
    Option.bind (offsets_signed_extrema offs) ~f:(fun (lo, hi) ->
        match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
        | Ok lo, Ok hi -> Some (lo, hi)
        | _ -> None)
  in
  match t with
  | Rel (Origin.Stack, offs) when word > 0 ->
    let w = Stdlib.Int64.of_int word in
    (match extrema_i64 offs with
     | Some (lo, _) when Stdlib.Int64.compare lo w >= 0 ->
       Rel (Origin.Window, offs)
     | _ -> t)
  | q -> q

(* The VLA value's entry-line hull: its frame-relative offsets shifted
   by the allocation base's range.  None when the base is unknown. *)
let vla_entry_hull (tid : Tid.t) (offs : P.t) : (int64 * int64) option =
  match vla_base_range tid, offsets_signed_extrema offs with
  | Some (blo, bhi), Some (lo, hi) -> (
    match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
    | Ok klo, Ok khi -> (
      match checked_add3 blo 0L klo, checked_add3 bhi 0L khi with
      | Some l, Some h when Stdlib.Int64.compare h l >= 0 -> Some (l, h)
      | _ -> None)
    | _ -> None)
  | _ -> None

let rec cardinality (t : t) : word =
  match t with
  | Clp ps -> P.cardinality ps
  | FinSet s -> FinSet.cardinality s
  | Rel (Origin.Vla _, offs) ->
    if P.is_bottom offs then Cbat_word.zero 65 else Cbat_word.ones 65
  (* An absolute-origin value's offsets ARE its absolute words: the
     base is the fixed 0, no segment multiplies. *)
  | Rel ((Origin.Abs | Origin.Rip _), offs) -> P.cardinality offs
  | Rel ((Origin.Stack | Origin.Window), offs) -> stack_cardinality offs
  | Many ps ->
    let width = Stdlib.max 65 (bitwidth t + 1) in
    List.fold ps ~init:(Cbat_word.zero width) ~f:(fun acc q ->
        let c = Cbat_word.cast Bil.UNSIGNED width (cardinality q) in
        let s = Cbat_word.add acc c in
        if Cbat_word.(<) s acc then Cbat_word.ones width else s)

(* Fold the leaves' extrema left-to-right, [better] picking the winner
   (ties go to the accumulator, matching the historical order). *)
let extremum (leaf : t -> word option)
    (better : Cbat_word.t -> Cbat_word.t -> Cbat_word.t) (t : t) : word option =
  let rec go acc (t : t) =
    match t with
    | Many ps -> List.fold ps ~init:acc ~f:go
    | q ->
      (match leaf q, acc with
       | None, acc -> acc
       | Some m, None -> Some m
       | Some m, Some a -> Some (better m a))
  in
  go None t

let min_elem (t : t) : word option =
  extremum
    (fun q ->
       match q with
       | Rel (o, offs) when absolute_line o -> P.min_elem offs
       | Rel (o, offs) ->
         Option.map (plain_bounds o offs) ~f:(fun (cmin, _) -> w64_of_i64 cmin)
       | Clp ps -> P.min_elem ps
       | FinSet s -> FinSet.min_elem s
       | Many _ -> None)
    (fun m a -> if Cbat_word.compare m a < 0 then m else a)
    t

let max_elem (t : t) : word option =
  extremum
    (fun q ->
       match q with
       | Rel (o, offs) when absolute_line o -> P.max_elem offs
       | Rel (o, offs) ->
         Option.map (plain_bounds o offs) ~f:(fun (_, cmax) -> w64_of_i64 cmax)
       | Clp ps -> P.max_elem ps
       | FinSet s -> FinSet.max_elem s
       | Many _ -> None)
    (fun m a -> if Cbat_word.compare m a > 0 then m else a)
    t

(* Stack-family extrema on the entry-relative offset line. *)
let offset_extrema (t : t) : (Cbat_word.t * Cbat_word.t) option =
  match t with
  | Rel (Origin.Vla tid, offs) ->
    Option.map (vla_entry_hull tid offs) ~f:(fun (lo, hi) ->
        (w64_of_i64 lo, w64_of_i64 hi))
  | Rel (o, offs) when Origin.names_stack_line o -> offsets_signed_extrema offs
  | _ -> None

let stack_bounds (t : t) : (int64 * int64) option =
  (* Stack-origin extrema on the offset line. *)
  Option.bind (offset_extrema t) ~f:(fun (lo, hi) ->
      match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
      | Ok loi, Ok hii -> Some (loi, hii)
      | _ -> None)


(* Signed extrema: the projection is signed-positive, so its signed
   and unsigned extrema agree; a set spanning the sign boundary has
   no signed extremum. *)
(* The signed extreme of one leaf; [dir] < 0 is the minimum, > 0 the
   maximum.  A sign-spanning piece has no signed extreme on that side. *)
let signed_leaf ~(dir : int) (q : t) : word option =
  let pick (a, b) = if dir < 0 then a else b in
  let clamp = if dir < 0 then Stdlib.Int64.min_int else Stdlib.Int64.max_int in
  let better m a =
    let c = Cbat_word.compare (Cbat_word.signed m) (Cbat_word.signed a) in
    if (if dir < 0 then c < 0 else c > 0) then m else a
  in
  let via_offsets_base base offs =
    Option.bind (offsets_signed_extrema offs)
      ~f:(fun ex ->
        Option.bind (checked_add3 base 0L
                       (match Cbat_word.to_int64 (pick ex) with
                        | Ok v -> v
                        | Error _ -> clamp))
          ~f:(fun v -> Some (w64_of_i64 v)))
  in
  let via_pieces ps =
    List.fold (P.to_list ps) ~init:None ~f:(fun acc p ->
        let r =
          match (if dir < 0 then Clp.min_elem_signed p
                 else Clp.max_elem_signed p) with
          | Some _ as r -> r
          | None ->
            if dir < 0 then
              (match Clp.max_elem p with
               | Some mx
                 when Cbat_word.(<) mx (Word_ops.half (Cbat_word.bitwidth mx)) ->
                 Clp.min_elem p
               | _ -> None)
            else
              (match Clp.min_elem p with
               | Some mn
                 when Cbat_word.(>=) mn (Word_ops.half (Cbat_word.bitwidth mn)) ->
                 Clp.max_elem p
               | _ -> None)
        in
        match r, acc with
        | None, acc -> acc
        | Some m, None -> Some m
        | Some m, Some a -> Some (better m a))
  in
  match q with
  | Rel (Origin.Vla tid, offs) -> (
    match vla_base_range tid with
    | Some (blo, bhi) -> (
      let base = if dir < 0 then blo else bhi in
      match checked_add3 stack_base base 0L with
      | Some abs -> via_offsets_base abs offs
      | None -> None)
    | None -> None)
  | Rel (o, offs) -> via_offsets_base (Origin.facts o).base offs
  | Clp ps -> via_pieces ps
  | FinSet s ->
    (if dir < 0 then FinSet.min_elem_signed s else FinSet.max_elem_signed s)
  | Many _ -> None

let extremum_signed ~(dir : int) (t : t) : word option =
  extremum (signed_leaf ~dir)
    (fun m a ->
       let c = Cbat_word.compare (Cbat_word.signed m) (Cbat_word.signed a) in
       if (if dir < 0 then c < 0 else c > 0) then m else a)
    t

let min_elem_signed (t : t) : word option = extremum_signed ~dir:(-1) t
let max_elem_signed (t : t) : word option = extremum_signed ~dir:1 t

(* Offset space: the per-sub cell-key universe keys by offsets. *)
let rec splits_by (t : t) (w : Cbat_word.t) =
  match t with
  | Clp offs | Rel (_, offs) -> P.splits_by offs w
  | FinSet s -> FinSet.splits_by s w
  | Many ps -> List.for_all ps ~f:(fun q -> splits_by q w)

(* Hull test: an over-approximation of membership in the projection. *)
let rec elem w (t : t) =
  match t with
  | Rel (o, offs) when absolute_line o -> P.elem w offs
  | Rel (o, offs) ->
    (match plain_bounds o offs with
     | Some (cmin, cmax) ->
       (match Cbat_word.to_int64 w with
        | Ok wi ->
          Stdlib.Int64.compare wi cmin >= 0
          && Stdlib.Int64.compare wi cmax <= 0
        | _ -> false)
     | None -> not (is_bottom t))
  | Clp ps -> P.elem w ps
  | FinSet s -> FinSet.elem w s
  | Many ps -> List.exists ps ~f:(fun q -> elem w q)

(* Materializes the base-0 slice only; the full projection is
   8 MiB of elements. *)
let rec iter (t : t) : word list =
  match t with
  | Rel (Origin.Vla tid, offs) -> (
    match vla_base_range tid with
    | Some (blo, _) -> (
      match checked_add3 stack_base blo 0L with
      | Some abs ->
        List.map (P.elements offs)
          ~f:(fun w -> Cbat_word.add (w64_of_i64 abs) w)
      | None -> [])
    | None -> [])
  (* An absolute-line value enumerates its offsets as they are. *)
  | Rel (o, offs) when absolute_line o -> P.elements offs
  | Rel (o, offs) ->
    List.map (P.elements offs)
      ~f:(fun w -> Cbat_word.add (w64_of_i64 (Origin.facts o).base) w)
  | Clp ps -> P.elements ps
  | FinSet s -> FinSet.iter s
  | Many ps -> List.concat_map ps ~f:iter

(* The fixpoint's convergence check calls this on every var of every
   visit: the leaf arms avoid the derived compare's list machinery. *)
let rec equal (t1 : t) (t2 : t) : bool =
  match t1, t2 with
  | Clp a, Clp b -> P.equal a b
  | FinSet a, FinSet b -> FinSet.equal a b
  | Rel (o1, a), Rel (o2, b) -> Origin.equal o1 o2 && P.equal a b
  | Many a, Many b ->
    List.length a = List.length b
    && List.for_all2_exn a b ~f:equal
  | _ -> false

let overlap (t1 : t) (t2 : t) : bool =
  let hull (ps : P.t) : clp =
    match hull_of_pieces ps with Some p -> p | None -> Clp.bottom 1 in
  let leaf_pair q1 q2 =
    match q1, q2 with
    | FinSet s1, FinSet s2 -> FinSet.overlap s1 s2
    | FinSet s1, Clp ps2 -> FinSet.overlap_generic (module Clp) s1 (hull ps2)
    | Clp ps1, FinSet s2 -> FinSet.overlap_generic (module Clp) s2 (hull ps1)
    | Clp ps1, Clp ps2 -> P.overlap ps1 ps2
    | _ -> false
  in
  match t1, t2 with
  | Rel (o1, a), Rel (o2, b) when Origin.equal o1 o2 -> P.overlap a b
  | _ -> match plain_view t1, plain_view t2 with
  | Many a, Many b ->
    List.exists a ~f:(fun q1 -> List.exists b ~f:(fun q2 -> leaf_pair q1 q2))
  | Many a, q2 -> List.exists a ~f:(fun q1 -> leaf_pair q1 q2)
  | q1, Many b -> List.exists b ~f:(fun q2 -> leaf_pair q1 q2)
  | q1, q2 -> leaf_pair q1 q2

(* ---------------- the plain binop distribution ---------------- *)

(* The plain binops as immediate tags: the lift's one op-aware choke
   point — every arm applies its op directly, no first-class function
   crosses the lift. *)
type binop =
  | Union
  | Meet
  | Add
  | Sub
  | Mul
  | Div
  | Sdiv
  | Modulo
  | Smodulo
  | Lshift
  | Rshift
  | Arshift
  | Logand
  | Logor
  | Logxor
  | Concat

(* The distributed arithmetic collapses to one progression: multi-piece
   results churn the fixpoint — the 4-piece cap is not associative
   under repeated joins, and in-loop values oscillate between
   incomparable capped forms (measured: five fresh fixpoint backstops on
   du and expr). *)
(* The 16-op table, written ONCE over a representation signature: the
   two concrete tables are instantiations, and the piece table's
   collapse is that representation's policy, applied by its
   instantiation. *)
module type Binop_repr = sig
  type t

  val union : t -> t -> t
  val meet : t -> t -> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val sdiv : t -> t -> t
  val modulo : t -> t -> t
  val smodulo : t -> t -> t
  val lshift : t -> t -> t
  val rshift : t -> t -> t
  val arshift : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val concat : t -> t -> t
end

module Binop (R : Binop_repr) = struct
  let binop (op : binop) (a : R.t) (b : R.t) : R.t =
    match op with
    | Union -> R.union a b
    | Meet -> R.meet a b
    | Add -> R.add a b
    | Sub -> R.sub a b
    | Mul -> R.mul a b
    | Div -> R.div a b
    | Sdiv -> R.sdiv a b
    | Modulo -> R.modulo a b
    | Smodulo -> R.smodulo a b
    | Lshift -> R.lshift a b
    | Rshift -> R.rshift a b
    | Arshift -> R.arshift a b
    | Logand -> R.logand a b
    | Logor -> R.logor a b
    | Logxor -> R.logxor a b
    | Concat -> R.concat a b
end

module Piece_repr = struct
  type t = P.t

  let union = P.union
  let meet = P.intersection
  let add = P.add
  let sub = P.sub
  let mul = P.mul
  let div = P.div
  let sdiv = P.sdiv
  let modulo = P.modulo
  let smodulo = P.smodulo
  let lshift = P.lshift
  let rshift = P.rshift
  let arshift = P.arshift
  let logand = P.logand
  let logor = P.logor
  let logxor = P.logxor
  let concat = P.concat
end

module Piece_binop = Binop (Piece_repr)

(* The distributed arithmetic collapses to one progression: multi-piece
   results churn the fixpoint -- the 4-piece cap is not associative
   under repeated joins, and in-loop values oscillate between
   incomparable capped forms (measured: five fresh fixpoint backstops on
   du and expr).  The interior exclusion a piece union can hold is lost
   here, not at the join; the widening's per-pair hull is where it is
   lost for fixpoint values.  The collapse is the piece representation's
   policy. *)
let binop_pieces (op : binop) (a : P.t) (b : P.t) : P.t =
  let collapse (ps : P.t) : P.t =
    match hull_of_pieces ps with
    | Some p -> P.of_progression p
    | None -> ps
  in
  collapse (Piece_binop.binop op a b)

module Fs_repr = struct
  type t = fset

  let union = FinSet.union
  let meet = FinSet.intersection
  let add = FinSet.add
  let sub = FinSet.sub
  let mul = FinSet.mul
  let div = FinSet.div
  let sdiv = FinSet.sdiv
  let modulo = FinSet.modulo
  let smodulo = FinSet.smodulo
  let lshift = FinSet.lshift
  let rshift = FinSet.rshift
  let arshift = FinSet.arshift
  let logand = FinSet.logand
  let logor = FinSet.logor
  let logxor = FinSet.logxor
  let concat = FinSet.concat
end

module Fs_binop = Binop (Fs_repr)

let binop_fs (op : binop) (s1 : fset) (s2 : fset) : fset =
  Fs_binop.binop op s1 s2

(* One op over one leaf pair; mixed kinds take the piece union of the
   FinSet's elements (exact runs), the operands in their own order. *)
(* The operand's representation decides the path: the exact finite set
   is the fast path, the piece union is the general one, and Rel/Many
   are opaque to the generic lift (the stack-aware ops route around
   it) — top. *)
type repr =
  | Fs of fset
  | Ps of P.t
  | Opaque

let repr_of (q : t) : repr =
  match q with
  | FinSet s -> Fs s
  | Clp ps -> Ps ps
  | Rel _ | Many _ -> Opaque

let op_pair (op : binop) (q1 : t) (q2 : t) : t list =
  let wide () = P.top (Stdlib.max (bitwidth q1) (bitwidth q2)) in
  match repr_of q1, repr_of q2 with
  | Fs s1, Fs s2 -> [ FinSet (binop_fs op s1 s2) ]
  | Ps a, Ps b -> [ Clp (binop_pieces op a b) ]
  | Ps ps, Fs s -> [ Clp (binop_pieces op ps (pieces_of_finset s)) ]
  | Fs s, Ps ps -> [ Clp (binop_pieces op (pieces_of_finset s) ps) ]
  | Opaque, _ | _, Opaque -> [ Clp (wide ()) ]

let lift_binop (op : binop) (t1 : t) (t2 : t) : t =
  match to_plain t1, to_plain t2 with
  | ((Clp _ | FinSet _ | Rel _) as q1),
    ((Clp _ | FinSet _ | Rel _) as q2) ->
    canonical (op_pair op q1 q2)
  | p1, p2 -> pairwise (op_pair op) p1 p2

let rec lift_unop (f_clp : P.t -> P.t) (f_fs : fset -> fset) : t -> t = fun t ->
  match t with
  | Clp ps -> canonical [ Clp (f_clp ps) ]
  | FinSet s -> canonical [ FinSet (f_fs s) ]
  | Rel _ as q ->
    (match to_plain q with
     | Clp ps -> canonical [ Clp (f_clp ps) ]
     | FinSet s -> canonical [ FinSet (f_fs s) ]
     | Rel _ | Many _ -> t)
  | Many ps -> canonical (List.map ps ~f:(fun q -> lift_unop f_clp f_fs q))

(* ---------------- stack queries ---------------- *)

(* The offset piece union of a stack-symbolic value — answers ONLY for
   the symbolic arm; a plain in-band set is None.  The single-progression
   view is the hull (the exact union is the piece list itself). *)
let stack_offsets (t : t) : Clp.t option =
  match t with
  | Rel (Origin.Vla tid, offs) -> (
    (* The frame-relative offsets shifted onto the entry line; an unknown
       base has no entry-line position (the sound fallback). *)
    match vla_entry_hull tid offs with
    | Some (lo, hi) ->
      Some (Clp.interval ~width:64 (w64_of_i64 lo) (w64_of_i64 hi))
    | None -> None)
  | Rel (o, offs) when Origin.names_stack_line o ->
    (match hull_of_pieces offs with
     | Some p -> Some p
     | None -> Some (Clp.bottom 64))
  | _ -> None

(* The frame-relative offsets of a VLA value (0 = the allocation base) —
   [Some] only for the [Vla] origin. *)
let vla_offsets (t : t) : Clp.t option =
  match t with
  | Rel (Origin.Vla _, offs) ->
    (match hull_of_pieces offs with
     | Some p -> Some p
     | None -> Some (Clp.bottom 64))
  | _ -> None

(* The memory-key coordinate line.  A stack access can land inside a
   VLA region (the allocation lives on the stack line), so [Stack],
   [Window], and [Vla] share one namespace; a module address names the
   same bytes as its absolute word, so [Rip] keys on the [Abs] line.
   The origin still rides the value; only the key line is coarsened. *)
let key_line (o : Origin.t) : Origin.t =
  match o with
  | Origin.Stack | Origin.Window | Origin.Vla _ -> Origin.Stack
  | Origin.Rip _ | Origin.Abs -> Origin.Abs

(* Memory keys retain the carried origin's line; plain values stay absolute. *)
let address_pieces (t : t) : (Origin.t * P.t) option =
  match t with
  | Rel (Origin.Vla tid, offs) -> (
    (* The memory key is the entry-line address: the frame-relative
       offsets shift by the allocation base's range; an unknown base
       keys the whole stack line (a stack access can land in the VLA). *)
    match vla_entry_hull tid offs with
    | Some (lo, hi) ->
      Some
        (Origin.Stack,
         P.of_progression
           (Clp.interval ~width:64 (w64_of_i64 lo) (w64_of_i64 hi)))
    | None -> Some (Origin.Stack, P.top 64))
  | Rel (o, offs) -> Some (key_line o, offs)
  | Clp ps -> Some (Origin.Abs, ps)
  | FinSet s -> Some (Origin.Abs, pieces_of_finset s)
  | Many _ -> None

(* A finite non-wrapped progression split at its value midpoint; a
   singleton has no halves. *)
let halves (p : clp) : (clp * clp) option =
  match Clp.min_elem p, Clp.max_elem p with
  | Some lo, Some hi when Cbat_word.(<) lo hi ->
    let one = Cbat_word.one (Cbat_word.bitwidth lo) in
    Some (Clp.split_at_n p (Cbat_word.add lo (Cbat_word.rshift (Cbat_word.sub hi lo) one)))
  | _ -> None

(* The elements of [t] [decide] keeps, bisected per progression on its
   memory key line: [decide line p] keeps or drops a whole
   sub-progression [p], or splits it; a singleton never splits, and an
   undecided one stays.  The origin is kept.  An unbounded piece, a
   frame-relative VLA value and a mixed-origin value are kept whole. *)
let filter_addresses (t : t)
    ~(decide : Origin.t -> clp -> [ `Keep | `Drop | `Split ]) : t =
  let rec bisect line acc (p : clp) =
    match decide line p with
    | `Keep -> p :: acc
    | `Drop -> acc
    | `Split ->
      (match halves p with
       | Some (a, b) -> bisect line (bisect line acc a) b
       | None -> p :: acc) in
  let filter line (ps : P.t) : P.t option =
    let progs = P.to_list ps in
    if List.exists progs ~f:Clp.is_infinite then None
    else
      let kept =
        List.fold progs ~init:[] ~f:(fun acc p ->
            List.fold (Clp.split_wrapped p) ~init:acc ~f:(bisect line)) in
      Some (List.fold kept ~init:(P.bottom (P.bitwidth ps))
              ~f:(fun acc p -> P.join acc (P.of_progression p))) in
  match t with
  | Rel (Origin.Vla _, _) | Many _ -> t
  | Rel (o, ps) ->
    Option.value_map (filter (key_line o) ps) ~default:t ~f:(fun ps -> Rel (o, ps))
  | Clp ps ->
    Option.value_map (filter Origin.Abs ps) ~default:t ~f:(fun ps -> canonical [ Clp ps ])
  | FinSet s ->
    let width = FinSet.bitwidth s in
    of_list ~width
      (List.filter (FinSet.iter s) ~f:(fun w ->
           match decide Origin.Abs (Clp.singleton w) with
           | `Drop -> false
           | `Keep | `Split -> true))

(* The value's own address stride: > 1 only when every piece shares one
   bounded stride; everything else is 1. *)
let stride (t : t) : int =
  let of_clp_pieces (ps : P.t) : int option =
    match P.to_list ps with
    | [] -> None
    | p :: rest ->
      if List.exists (p :: rest) ~f:Clp.is_infinite then None
      else
        let s = Clp.step_of p in
        if List.for_all rest ~f:(fun q -> Cbat_word.equal (Clp.step_of q) s)
        then
          (match Cbat_word.to_int64 s with
           | Ok i
             when Stdlib.Int64.compare i 1L > 0
                  && Stdlib.Int64.compare i
                       (Stdlib.Int64.of_int Stdlib.max_int) <= 0 ->
             Some (Stdlib.Int64.to_int i)
           | _ -> None)
        else None
  in
  let leaf_stride (q : t) : int option =
    match q with
    | Clp ps | Rel (_, ps) -> of_clp_pieces ps
    | FinSet s ->
      (match FinSet.iter s with
       | [] | [ _ ] -> Some 1
       | w1 :: rest ->
         let rec common_diff prev d = function
           | [] -> d
           | w :: tl ->
             let d' = Cbat_word.sub w prev in
             if Cbat_word.is_zero d' then None
             else
               match d with
               | None -> common_diff w (Some d') tl
               | Some d0 ->
                 if Cbat_word.equal d0 d' then common_diff w d tl else None
         in
         (match common_diff w1 None rest with
          | Some d ->
            (match Cbat_word.to_int64 d with
             | Ok i ->
               let v = Stdlib.Int64.to_int i in
               if v > 1 then Some v else Some 1
             | Error _ -> Some 1)
          | None -> Some 1))
    | Many _ -> None
  in
  match t with
  | Many ps ->
    (match List.map ps ~f:leaf_stride with
     | [] -> 1
     | strides ->
       if List.for_all strides ~f:(function Some _ -> true | None -> false)
       then
         let s =
           match
             List.find strides ~f:(function
               | Some _ -> true | None -> false)
           with
           | Some (Some s) -> s
           | _ -> 1
         in
         if
           List.for_all strides ~f:(function
             | Some s' -> Stdlib.( = ) s s'
             | None -> false)
         then s
         else 1
       else 1)
  | q ->
    (match leaf_stride q with
     | Some s -> s
     | None -> 1)

(* THE per-op type table: what [op] yields when its operands meet at
   origins [o1] and [o2] (an absolute operand is [Origin.Abs]).
   [Wrap o] = the offsets stay relative at [o]; [Materialise] = the
   bases do not survive — both hulls, the plain op; [Top] = the op
   keeps unknown base bits: top.  THE table is the one home of "what
   type dominates"; a new origin lands by extending [Origin.t], a new
   op by one row here.  The two entry-line origins absorb onto
   [Stack]; a VLA frame never merges — its offsets are frame-relative,
   so a cross-origin op materialises through the base range (or tops). *)
let origin_is_relative x = not (absolute_line x)

let rel_table (op : binop) (o1 : Origin.t) (o2 : Origin.t) :
    Hike_origin.rel_row =
  let rel x = origin_is_relative x in
  let cross_line =
    rel o1 && rel o2 && not (Origin.equal o1 o2)
    && (match o1, o2 with
        | Origin.Vla _, _ | _, Origin.Vla _ -> false
        | _ -> Origin.names_stack_line o1 && Origin.names_stack_line o2)
  in
  match op with
  | Union ->
    if rel o1 && rel o2 then
      if Origin.equal o1 o2 then Wrap o1
      else if cross_line then Wrap Origin.Stack
      else Materialise
    else Materialise
  | Meet ->
    if rel o1 && rel o2 then
      if Origin.equal o1 o2 then Wrap o1
      else if cross_line then Wrap Origin.Stack
      else Materialise
    else if rel o1 then Wrap o1
    else if rel o2 then Wrap o2
    else Materialise
  | Add | Sub ->
    if rel o1 && rel o2 then Materialise
    (* the base appears twice [Add] / cancels [Sub]; a relative operand
       shifts its offsets by the absolute one *)
    else if rel o1 then Wrap o1
    else if rel o2 then (match op with Sub -> Top | _ -> Wrap o2)
    else Materialise
  | Logand ->
    if rel o1 && rel o2 then Top
    else if rel o1 then Wrap o1
    else if rel o2 then Wrap o2
    else Materialise
  | Mul | Div | Sdiv | Modulo | Smodulo
  | Lshift | Rshift | Arshift | Logor | Logxor | Concat ->
    if rel o1 || rel o2 then Top else Materialise

(* The Top rows' width: concat's result is the concatenated width. *)
let top_width (op : binop) (w1 : int) (w2 : int) : int =
  match op with Concat -> w1 + w2 | _ -> Stdlib.max w1 w2

(* The same-origin payload: the op on the offset piece unions — the
   piece ops run bare (no collapse: the relative unions keep their
   exact runs). *)
let rel_rel (op : binop) (a : P.t) (b : P.t) : P.t =
  match op with
  | Union -> P.union a b
  | Meet -> P.intersection a b
  | _ -> binop_pieces op a b

(* The [Materialise] payload: both hulls, the plain op; [Sub]'s
   relative-relative row keeps the exact offset difference (the base
   cancels — no collapse). *)
let materialise2 (op : binop) (t1 : t) (t2 : t) : t =
  match op, t1, t2 with
  | Sub, Rel (o1, a), Rel (o2, b) when Origin.equal o1 o2 ->
    canonical [ Clp (P.sub a b) ]
  | _ -> lift_binop op (to_plain t1) (to_plain t2)

let has_relative (t : t) : bool =
  match t with
  | Rel (o, _) -> origin_is_relative o
  | Many ps -> List.exists ps ~f:(function Rel (o, _) -> origin_is_relative o | _ -> false)
  | _ -> false


(* Translate a plain constraint into the carried origin's offset space. *)
let plain_offsets (o : Origin.t) (p : t) : P.t option =
  let base = Cbat_word.of_int64 ~width:64 (Origin.facts o).base in
  match p with
  | Clp ps when not (P.is_bottom ps) ->
    Some (P.translate ps (Cbat_word.neg base))
  | FinSet s ->
    let ws = List.map ~f:(fun w -> Cbat_word.sub w base) (FinSet.iter s) in
    (match ws with
     | [] -> Some (P.bottom 64)
     | _ -> Some (pieces_of_words ~width:64 ws))
  | _ -> None


(* The singleton word of a plain operand, if it is one. *)
let singleton_of (q : t) : word option =
  let pair a b = if Cbat_word.equal a b then Some a else None in
  match q with
  | Clp ps ->
    (match P.min_elem ps, P.max_elem ps with
     | Some a, Some b -> pair a b
     | _ -> None)
  | FinSet s ->
    (match FinSet.min_elem s, FinSet.max_elem s with
     | Some a, Some b -> pair a b
     | _ -> None)
  | Rel _ | Many _ -> None


(* [f] over the offsets while enumerable; top past the budget. *)
let certified_image ~(origin : Origin.t) ~(width : int) (f : word -> word) (offs : P.t) : t =
  let base = w64_of_i64 ((base_facts origin).base) in
  match Cbat_word.to_int (P.cardinality offs) with
  | Ok n when n > 0 && n <= Utils.fin_set_size ->
    of_list ~width
      (List.map (P.elements offs)
         ~f:(fun o ->
             Cbat_word.cast Bil.UNSIGNED width (f (Cbat_word.add base o))))
  | _ -> top width


(* The round-down mask class: [k = ~m] with [m = 2^s - 1] (all-ones is
   s = 64, the identity).  The shift the mask implies, if [k] is one. *)
let round_down_shift (k : word) : int option =
  if Cbat_word.equal k (Cbat_word.ones 64) then Some 64
  else
    let m = Cbat_word.sub (Cbat_word.ones 64) k in
    let m1 = Cbat_word.add m (Cbat_word.one 64) in
    if Cbat_word.is_zero m1 then None
    else if Cbat_word.is_zero (Cbat_word.logand m m1) then
      let rec count v acc =
        if Cbat_word.is_zero v then Some acc
        else count (Cbat_word.rshift v (Cbat_word.one 64)) (acc + 1)
      in
      count m 0
    else None

(* Round offsets using the carried base's certified residue. A VLA's
   routing floor expands by the possible alignment slack. *)
let round_down_image_for (o : Origin.t) (s : int) (offs : P.t) : P.t option =
  if s >= 64 then Some offs
  else if s > (base_facts o).certified then
    let slack = Cbat_word.sub (Cbat_word.lshift (Cbat_word.one 64)
        (Cbat_word.of_int ~width:64 s)) (Cbat_word.one 64) in
    (match o, Cbat_word.to_int64 slack with
     | Origin.Vla tid, Ok m -> Origin.Vla_seed.widen_off_lo tid (Stdlib.Int64.neg m)
     | _ -> ());
    Some (P.sub offs (P.of_progression
        (Clp.interval ~width:64 (Cbat_word.zero 64) slack)))
  else
    let m64 = Stdlib.Int64.pred (Stdlib.Int64.shift_left 1L s) in
    let b_lo = Stdlib.Int64.logand ((base_facts o).base) m64 in
    let block (w : word) =
      match Cbat_word.to_int64 w with
      | Error _ -> None
      | Ok v ->
        let r = Stdlib.Int64.logand (Stdlib.Int64.add b_lo v) m64 in
        Some (Cbat_word.of_int64 ~width:64 (Stdlib.Int64.sub v r))
    in
    let seed () =
      match o with
      | Origin.Vla tid -> Origin.Vla_seed.widen_off_lo tid (Stdlib.Int64.neg m64)
      | _ -> ()
    in
    seed ();
    let step =
      Cbat_word.of_int64 ~width:64 (Stdlib.Int64.shift_left 1L s)
    in
    let imgs =
      List.filter_map (P.to_list offs) ~f:(fun g ->
          match Clp.min_elem g, Clp.max_elem g with
          | Some a, Some b -> (
              match block a, block b with
              | Some a', Some b' ->
                let span65 =
                  Cbat_word.cast Bil.UNSIGNED 65 (Cbat_word.sub b' a')
                in
                let cnt =
                  Cbat_word.add
                    (Cbat_word.rshift span65 (Cbat_word.of_int ~width:65 s))
                    (Cbat_word.one 65)
                in
                Some (Clp.create a' ~step ~cardn:cnt)
              | _ -> None)
          | _ -> None)
    in
    let rec union_all = function
      | [] -> P.bottom 64
      | [ g ] -> P.of_progression g
      | g :: rest -> P.union (P.of_progression g) (union_all rest)
    in
    if List.length imgs = List.length (P.to_list offs) then
      Some (union_all imgs)
    else None

(* The plain meet: every leaf pair contributes its exact intersection (a
   relative leaf materialises — the meet is an over-approximation, the
   hull is sound), and the results merge.  The cross product is the
   exact meet: a kind carried by one side only must still meet the other
   side's leaves. *)
let meet_plain (t1 : t) (t2 : t) : t =
  let pair q1 q2 =
    let q1 = match q1 with Rel _ -> to_plain q1 | q -> q in
    let q2 = match q2 with Rel _ -> to_plain q2 | q -> q in
    match q1, q2 with
    | FinSet s1, FinSet s2 -> [ FinSet (FinSet.intersection s1 s2) ]
    | FinSet s, Clp ps | Clp ps, FinSet s ->
      [ FinSet
          (FinSet.of_list ~width:(FinSet.bitwidth s)
             (List.filter (FinSet.iter s)
                ~f:(fun w -> P.elem w ps))) ]
    | Clp ps1, Clp ps2 -> [ Clp (P.intersection ps1 ps2) ]
    | _ -> []
  in
  pairwise pair t1 t2

(* The plain join: every leaf pair contributes — two Clp leaves the exact
   piece union, two FinSet leaves the exact union, a one-sided kind its
   own leaf — so the join never hulls. *)
let join_plain (t1 : t) (t2 : t) : t =
  let rel_op o1 a o2 b =
    if Origin.equal o1 o2 then Rel (o1, P.union a b)
    else
      Clp
        (P.union
           (P.of_progression (as_clp (Rel (o1, a))))
           (P.of_progression (as_clp (Rel (o2, b)))))
  in
  pair_join ~clp_op:P.union ~fs_op:FinSet.union ~rel_op t1 t2

(* The plain-plain payload: the lattice ops pair by kind; every other op
   lifts through the common plain machinery. *)
let generic (op : binop) (t1 : t) (t2 : t) : t =
  match op with
  | Meet -> meet_plain t1 t2
  | Union -> join_plain t1 t2
  | _ -> lift_binop op t1 t2

(* The [Wrap] payloads: the relative operand's offsets meet, shift, or
   mask with the absolute one, and the result wraps at the operand's
   origin. *)
let has_fixed_base = function
  | Origin.Abs | Origin.Rip _ | Origin.Stack | Origin.Window -> true
  | Origin.Vla _ -> false

let meet_rel (t1 : t) (t2 : t) : t =
  match t1, t2 with
  | Rel (o, a), (Clp _ | FinSet _ as plain) when has_fixed_base o ->
    (match plain_offsets o plain with
     | Some o2 -> canonical [ Rel (o, P.intersection a o2) ]
     | None -> meet_plain (to_plain t1) (to_plain plain))
  | (Clp _ | FinSet _ as plain), Rel (o, a) when has_fixed_base o ->
    (match plain_offsets o plain with
     | Some o2 -> canonical [ Rel (o, P.intersection a o2) ]
     | None -> meet_plain (to_plain plain) (to_plain t2))
  | _ -> meet_plain (to_plain t1) (to_plain t2)

let logand_rel (o : Origin.t) (offs : P.t) (plain : t) : t =
  let certified_bits = (base_facts o).certified in
  match singleton_of plain with
  | Some k -> (
      match round_down_shift k with
      | Some s -> (
          match round_down_image_for o s offs with
          | Some offs' -> canonical [ Rel (o, offs') ]
          | None -> top 64)
      | None ->
        if certified_bits >= 64 || Cbat_word.leq_int k ((1 lsl certified_bits) - 1) then
          let k64 = Cbat_word.cast Bil.UNSIGNED 64 k in
          certified_image ~origin:o ~width:64 (fun v -> Cbat_word.logand v k64) offs
        else top 64)
  | None -> top 64

let rel_abs (op : binop) (t1 : t) (t2 : t) : t =
  match op with
  | Add | Sub ->
    let f = match op with Sub -> Clp.sub | _ -> Clp.add in
    let hull (ps : P.t) : clp =
      match hull_of_pieces ps with
      | Some p -> p
      | None -> Clp.bottom 64
    in
    let hull_of_plain (q : t) : clp option =
      match q with
      | Clp ps -> hull_of_pieces ps
      | FinSet s -> Some (clp_of_finset s)
      | _ -> None
    in
    (match t1, t2 with
     | Rel (o, a1), q2 when bitwidth q2 = 64 ->
       (match hull_of_plain q2 with
        | Some p2 -> canonical [ Rel (o, P.of_progression (f (hull a1) p2)) ]
        | None -> lift_binop op t1 t2)
     | q1, Rel (o, a2) when bitwidth q1 = 64 ->
       (match hull_of_plain q1 with
        | Some p1 -> canonical [ Rel (o, P.of_progression (f p1 (hull a2))) ]
        | None -> lift_binop op t1 t2)
     | _ -> lift_binop op t1 t2)
  | Meet -> meet_rel t1 t2
  | Logand -> (
      match t1, t2 with
      | Rel (o, offs), plain -> logand_rel o offs plain
      | plain, Rel (o, offs) -> logand_rel o offs plain
      | _ -> top (Stdlib.max (bitwidth t1) (bitwidth t2)))
  | Union -> materialise2 op t1 t2
  | _ -> lift_binop op t1 t2

(* A module address keeps its region through pointer arithmetic: an
   absolute displacement added or subtracted, a mask, or a refinement.
   Every other op computes on the link-time words, which the absolute
   line makes exact. *)
let rip_keeps (op : binop) ~(left : bool) : bool =
  match op with
  | Add | Logand | Meet -> true
  | Sub -> left
  | _ -> false

(* The exact plain twin of a module address's offsets. *)
let rip_plain (offs : P.t) : t = canonical [ Clp offs ]

(* Re-tags a plain address-width result with section [p]. *)
let rip_wrap (p : Hike_section.t) (t : t) : t =
  if bitwidth t <> 64 then t
  else
    canonical
      (List.map (leaves t) ~f:(function
         | Clp ps -> Rel (Origin.Rip p, ps)
         | FinSet s -> Rel (Origin.Rip p, pieces_of_finset s)
         | q -> q))

(* A plain computation over two module addresses of one section stays in
   that section: the absolute line makes the re-tag exact. *)
let keep_section ~(old : t) ~(new_ : t) (r : t) : t =
  match origin old, origin new_ with
  | Some (Origin.Rip p), Some (Origin.Rip p') when Hike_section.equal p p' ->
    rip_wrap p r
  | _ -> r

let blind_unop (f_clp : P.t -> P.t) (f_fs : fset -> fset) (t : t) : t =
  if has_relative t then top (Stdlib.max 1 (bitwidth t))
  else lift_unop f_clp f_fs t

(* The unary op ADT: the certified-nibble family over one operand.
   [Extract] carries hi as written (the [Some 63] identity test reads
   the option, not the default) and the defaulted lo. *)
type unop =
  | Lnot
  | Neg
  | Extract of int option * int
  | Cast of Bil.cast * int

(* THE unary table: the certified-nibble law, per origin — [Wrap] = the
   identity, [Image] = the certified image of the offsets into the
   plain tier, [Top] = the op keeps unknown base bits. *)
let unop_table (op : unop) ~(origin : Origin.t) : Hike_origin.un_row =
  let certified_bits = (base_facts origin).certified in
  match op with
  | Lnot | Neg -> Top
  | Extract (hi, lo) ->
    if lo = 0 && (match hi with Some 63 -> true | _ -> false) then Wrap
    else if Option.value ~default:63 hi < certified_bits then Image
    else Top
  | Cast (c, sz) ->
    if sz = 64 then Wrap
    else if sz <= certified_bits && not (match c with Bil.HIGH -> true | _ -> false)
    then Image
    else Top

(* THE general unary operator: the table decides the row, the payload
   computes once, the row wraps the result. *)
let rec lift1 (op : unop) (t : t) : t =
  let top_w () =
    match op with
    | Extract (hi, lo) -> top (Option.value ~default:63 hi - lo + 1)
    | Cast (_, sz) -> top sz
    | _ -> top (Stdlib.max 1 (bitwidth t))
  in
  match op, t with
  (* Degenerate ranges keep top. *)
  | Extract (Some hi, lo), _ when hi < lo -> top (Stdlib.max 1 (bitwidth t))
  | Cast (_, sz), _ when sz <= 0 -> top (Stdlib.max 1 (bitwidth t))
  | _, _ ->
  match t with
  | Rel (Origin.Abs, offs) -> plain_unop op (Clp offs)
  | Rel (Origin.Rip _, _) as v when (match op with
      | Extract (Some 63, 0) | Cast (_, 64) -> true
      | _ -> false) -> v
  | Rel (Origin.Rip _, offs) -> plain_unop op (rip_plain offs)
  | Rel (o, offs) as v -> (
      let image () =
        match op with
        | Extract (hi, lo) ->
          let hi_v = Option.value ~default:63 hi in
          certified_image ~origin:o ~width:(hi_v - lo + 1)
            (Cbat_word.extract_exn ~hi:hi_v ~lo:lo) offs
        | Cast (c, sz) ->
          certified_image ~origin:o ~width:sz (Cbat_word.cast c sz) offs
        | Lnot | Neg -> top_w ()
      in
      match unop_table op ~origin:o with
      | Wrap -> v
      | Image -> image ()
      | Top -> top_w ())
  | _ -> plain_unop op t

(* The plain-plain payload: the op over the plain leaves. *)
and plain_unop (op : unop) (t : t) : t =
  match op with
  | Extract (hi, lo) ->
    lift_unop
      (P.extract ?hi ?lo:(Some lo))
      (FinSet.extract ?hi ?lo:(Some lo)) t
  | Cast (c, sz) -> lift_unop (P.cast c sz) (FinSet.cast c sz) t
  | Lnot -> blind_unop P.lnot FinSet.lnot t
  | Neg -> blind_unop P.neg FinSet.neg t

(* THE general binary operator: the operands classify by pattern (a
   relative leaf allocates nothing), the table decides the row, the
   payload computes once, and the row wraps the result. *)
let rec lift2 (op : binop) (t1 : t) (t2 : t) : t =
  let top_w () = top (top_width op (bitwidth t1) (bitwidth t2)) in
  match op with
  (* The precise meet across representations: a width mismatch returns
     the wider operand; a top plain side makes the meet the relative
     operand itself. *)
  | Meet when bitwidth t1 <> bitwidth t2 -> if bitwidth t1 > bitwidth t2 then t1 else t2
  | Meet when (match t1 with Rel _ -> plain_is_top t2 | _ -> false) -> t1
  | Meet when (match t2 with Rel _ -> plain_is_top t1 | _ -> false) -> t2
  (* The shift count's width is incidental: a narrower plain count
     zero-extends to the shifted operand's width (the machine masks the
     count; the lift's count value is already masked). *)
  | Lshift | Rshift | Arshift
    when bitwidth t2 < bitwidth t1
         && (match t2 with Rel _ | Many _ -> false | _ -> true) ->
    lift2 op t1 (lift1 (Cast (Bil.UNSIGNED, bitwidth t1)) t2)
  | _ ->
  match t1, t2 with
  | Rel (Origin.Abs, offs), _ -> lift2 op (Clp offs) t2
  | _, Rel (Origin.Abs, offs) -> lift2 op t1 (Clp offs)
  | Rel (Origin.Rip p, a), Rel (Origin.Rip p', b)
    when Hike_section.equal p p' && (match op with Union | Meet -> true | _ -> false) ->
    rip_wrap p (lift2 op (rip_plain a) (rip_plain b))
  | Rel (Origin.Rip p, a), (Clp _ | FinSet _) when rip_keeps op ~left:true ->
    rip_wrap p (lift2 op (rip_plain a) t2)
  | (Clp _ | FinSet _), Rel (Origin.Rip p, b) when rip_keeps op ~left:false ->
    rip_wrap p (lift2 op t1 (rip_plain b))
  | Rel (Origin.Rip _, a), _ -> lift2 op (rip_plain a) t2
  | _, Rel (Origin.Rip _, b) -> lift2 op t1 (rip_plain b)
  | _ -> if
    (match op with
     | Mul | Div | Sdiv | Modulo | Smodulo | Lshift | Rshift | Arshift
     | Logor | Logxor | Concat ->
       has_relative t1 || has_relative t2
     | _ -> false)
  then top_w ()
  else
    match t1, t2 with
    | Rel (o1, a1), Rel (o2, a2) -> (
        match rel_table op o1 o2 with
        | Wrap o -> canonical [ Rel (o, rel_rel op a1 a2) ]
        | Materialise -> materialise2 op t1 t2
        | Top -> top_w ())
    | Rel (o1, _), _ -> (
        match rel_table op o1 Origin.Abs with
        | Wrap _ -> rel_abs op t1 t2
        | Materialise -> materialise2 op t1 t2
        | Top -> top_w ())
    | _, Rel (o2, _) -> (
        match rel_table op Origin.Abs o2 with
        | Wrap _ -> rel_abs op t1 t2
        | Materialise -> materialise2 op t1 t2
        | Top -> top_w ())
    | _ -> generic op t1 t2

let union t1 t2 : t = lift2 Union t1 t2

let intersection t1 t2 : t = lift2 Meet t1 t2

(* Difference refines only a shared offset line or an exact plain
   constraint. Materializing the subtrahend could erase reachable values. *)
let rec diff (t1 : t) (t2 : t) : t =
  if bitwidth t1 <> bitwidth t2 then t1 else
  match t1, t2 with
  | Rel (Origin.Abs, offs), _ -> diff (Clp offs) t2
  | _, Rel (Origin.Abs, offs) -> diff t1 (Clp offs)
  | Rel (o1, a), Rel (o2, b)
    when Origin.equal o1 o2
         || (has_fixed_base o1 && has_fixed_base o2
             && Int64.equal (Origin.facts o1).base (Origin.facts o2).base) ->
    canonical [ Rel (o1, P.diff a b) ]
  | _, Rel (Origin.Rip _, b) -> diff t1 (rip_plain b)
  | _, Rel _ -> t1
  | Rel (o, offs), plain ->
    if has_fixed_base o then
      (match plain_offsets o plain with
       | Some constraint_ -> canonical [ Rel (o, P.diff offs constraint_) ]
       | None -> t1)
    else t1
  | _ ->
    let pair q1 q2 =
      if bitwidth q1 <> bitwidth q2 then [ q1 ]
      else
        match q1, q2 with
        | FinSet s1, FinSet s2 -> [ FinSet (FinSet.diff s1 s2) ]
        | FinSet s, Clp ps ->
          [ FinSet
              (FinSet.of_list ~width:(FinSet.bitwidth s)
                 (List.filter (FinSet.iter s)
                    ~f:(fun w -> not (P.elem w ps)))) ]
        | Clp ps, FinSet s -> [ Clp (P.diff ps (pieces_of_finset s)) ]
        | Clp ps1, Clp ps2 -> [ Clp (P.diff ps1 ps2) ]
        | _ -> []
    in
    pairwise pair t1 t2


let add t1 t2 : t = lift2 Add t1 t2
let sub t1 t2 : t = lift2 Sub t1 t2
let mul t1 t2 = lift2 Mul t1 t2
let div t1 t2 = lift2 Div t1 t2
let sdiv t1 t2 = lift2 Sdiv t1 t2
let modulo t1 t2 = lift2 Modulo t1 t2
let smodulo t1 t2 = lift2 Smodulo t1 t2

let logand t1 t2 : t = lift2 Logand t1 t2
let logor t1 t2 = lift2 Logor t1 t2
let logxor t1 t2 = lift2 Logxor t1 t2

let lnot t = lift1 Lnot t
let neg t = lift1 Neg t


let concat t1 t2 = lift2 Concat t1 t2

(* ---------------- predicates ---------------- *)

let is_top t =
  match t with
  | Clp ps | Rel (_, ps) -> P.is_top ps
  | FinSet _ -> false
  | Many ps ->
    List.for_all ps ~f:(function
      | Clp ps | Rel (_, ps) -> P.is_top ps
      | _ -> false)
    && List.exists ps ~f:(function
        | Clp _ | Rel _ -> true
        | _ -> false)

let piece_is_infinite (q : t) =
  match q with
  | Clp ps | Rel (_, ps) ->
    List.exists (P.to_list ps) ~f:Clp.is_infinite
  | FinSet _ -> false
  | Many _ -> false

let is_infinite t =
  match t with
  | Many ps ->
    (match ps with
     | [] -> false
     | _ -> List.for_all ps ~f:piece_is_infinite)
  | q -> piece_is_infinite q

let shape_pred (which : Clp.t -> bool) (t : t) : bool =
  let leaf q =
    match q with
    | Clp ps | Rel (_, ps) -> List.for_all (P.to_list ps) ~f:which
    | FinSet _ -> false
    | Many _ -> false
  in
  match t with
  | Many ps ->
    (match ps with
     | [] -> false
     | _ -> List.for_all ps ~f:leaf)
  | q -> leaf q

let is_ascending t = shape_pred Clp.is_ascending t
let is_descending t = shape_pred Clp.is_descending t
let is_circular t = shape_pred Clp.is_circular t

let rec precedes t1 t2 : bool =
  match t1, t2 with
  | Rel (o1, a), Rel (o2, b) when Origin.equal o1 o2 -> P.precedes a b
  | _, Rel _ -> is_bottom t1
  | Rel _, _ -> precedes (to_plain t1) t2
  | Clp p1, Clp p2 -> P.precedes p1 p2
  | FinSet s1, FinSet s2 -> FinSet.precedes s1 s2
  | Clp _, FinSet _ -> false
  | FinSet s, Clp _ -> Clp.precedes (clp_of_finset s) (as_clp t2)
  | _ -> Clp.precedes (as_clp t1) (as_clp t2)

(* Values with the same origin widen in its offsets.
   A plain pair widens BY KIND — two Clp leaves via [fp] (the positional
   piece widen), two FinSet leaves via the tier's own widen, two
   relative leaves via the offsets widen — so a multi-piece value keeps
   its pieces through a growing widen (the interior exclusion survives).
   A kind carried by one side only (the excess) hulls the whole pair —
   a widening must extrapolate, and the hull is the sound
   extrapolation. *)
let hull_join (f : Clp.t -> Clp.t -> Clp.t) (fp : P.t -> P.t -> P.t) t1 t2 : t =
  (* The absolute hull of two relative leaves: different origins have no
     shared offset line, so both materialise. *)
  let rel_cross (o1 : Origin.t) (a : P.t) (o2 : Origin.t) (b : P.t) : t =
    if Origin.equal o1 o2 then Rel (o1, fp a b)
    else
      Clp (P.of_progression (f (as_clp (Rel (o1, a))) (as_clp (Rel (o2, b)))))
  in
  let plain_hull () =
    canonical [ Clp (P.of_progression (f (as_clp t1) (as_clp t2))) ]
  in
  (* The FinSet tier widens by its own union while the union stays put;
     a union that grew has left the exact-small tier, so it escapes to
     the piece widen (the tier promotion the spec's Risks names) and the
     widening still extrapolates. *)
  let fs_widen (s1 : fset) (s2 : fset) : t =
    let u = FinSet.widen_join s1 s2 in
    if FinSet.equal u s1 then FinSet u
    else Clp (fp (pieces_of_finset s1) (pieces_of_finset s2))
  in
  (* Both sides plain: every kind carried by BOTH sides pairs with its
     own widen; a kind carried by one side only (the excess) hulls the
     whole pair — a one-sided piece has no partner to widen against, and
     a piece-preserving fold of it is the fixpoint's churn source. *)
  let plain_pair () =
    let c1 = clp_leaf t1 and c2 = clp_leaf t2 in
    let s1 = fs_leaf t1 and s2 = fs_leaf t2 in
    let r1 = rel_leaf t1 and r2 = rel_leaf t2 in
    let has o = Option.is_some o in
    if
      Stdlib.Int.equal (bitwidth t1) (bitwidth t2)
      && Bool.equal (has c1) (has c2)
      && Bool.equal (has s1) (has s2)
      && Bool.equal (has r1) (has r2)
    then
      let parts =
        (match c1, c2 with Some a, Some b -> [ Clp (fp a b) ] | _ -> [])
        @ (match s1, s2 with Some a, Some b -> [ fs_widen a b ] | _ -> [])
        @ (match r1, r2 with
           | Some (o1, a), Some (o2, b) -> [ rel_cross o1 a o2 b ]
           | _ -> [])
      in
      if List.is_empty parts then plain_hull () else canonical parts
    else plain_hull ()
  in
  match t1, t2 with
  | Rel (o1, a), Rel (o2, b) when Origin.equal o1 o2 ->
    canonical [ Rel (o1, fp a b) ]
  | _ -> plain_pair ()

let widen_join t1 t2 : t = hull_join Clp.widen_join P.widen_join t1 t2

let extrapolate_steps ~steps t1 t2 : t =
  hull_join
    (Clp.extrapolate_steps ~steps)
    (fun a b -> P.extrapolate_steps ~steps a b)
    t1 t2

let join = union
let meet = intersection

let extract ?hi ?lo t = lift1 (Extract (hi, Option.value ~default:0 lo)) t
let cast c sz t = lift1 (Cast (c, sz)) t

let arshift t1 t2 = lift2 Arshift t1 t2
let rshift t1 t2 = lift2 Rshift t1 t2
let lshift t1 t2 = lift2 Lshift t1 t2


let rec get_idx (t : t) : idx =
  match t with
  | Rel _ -> 64
  | Clp ps ->
    (match hull_of_pieces ps with
     | Some p -> Clp.get_idx p
     | None -> 0)
  | FinSet s -> FinSet.get_idx s
  | Many ps ->
    List.fold ps ~init:0 ~f:(fun a q -> Stdlib.max a (get_idx q))

let pp_leaf ppf (t : t) =
  match t with
  | Rel (o, offs) ->
    Format.fprintf ppf "@[%s%a@]" (Origin.name o) (fun ppf ps ->
        match hull_of_pieces ps with
        | Some p -> Clp.pp ppf p
        | None -> ())
    offs
  | Clp ps ->
    (match hull_of_pieces ps with
     | Some p -> Clp.pp ppf p
     | None -> Format.fprintf ppf "_|_")
  | FinSet s -> FinSet.pp ppf s
  | Many _ -> ()

let pp ppf (t : t) =
  match t with
  | Many ps ->
    Format.fprintf ppf "@[<1>(%a)@]"
      (fun ppf ts ->
        List.iter ts ~f:(fun q -> Format.fprintf ppf "@;%a" pp_leaf q))
      ps
  | q -> pp_leaf ppf q


(* The def-carried classification of a set on the model's ABSOLUTE
   segment line — the entry RSP is the segment base, so a frame offset
   o has absolute position [stack_base + o]. *)

type kind =
  | Range of int64 * int64
  | Infinite of int64 * int64
  | Caller of int64 * int64
  | Mixed of int64 * int64
[@@deriving equal]

(* The fully-infinite span: the whole position line.  A TOP denotation
   IS this span — the degenerate [Infinite], carrying no bound. *)
let unbounded_span : kind = Infinite (Stdlib.Int64.min_int, Stdlib.Int64.max_int)

let is_unbounded_span (lo : int64) (hi : int64) : bool =
  Int64.equal lo Stdlib.Int64.min_int && Int64.equal hi Stdlib.Int64.max_int

(* Overflow-checked absolute position of one frame offset. *)
let position_of_offset (o : int64) : int64 option =  checked_add3 stack_base 0L o

(* The per-progression [min, max] positions of a stack-symbolic value's
   offsets — the disjoint runs the attribution clips per run instead of
   hulling (a two-band address keeps both bands in the portions). *)
let offset_runs (t : t) : (int64 * int64) list =
  match t with
  | Rel (o, offs) when Origin.names_stack_line o ->
    List.filter_map (P.to_list offs) ~f:(fun g ->
        let bounds =
          match o with
          | Origin.Vla tid -> vla_entry_hull tid (P.of_progression g)
          | _ ->
            Option.bind (offsets_signed_extrema (P.of_progression g))
              ~f:(fun (lo, hi) ->
                match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
                | Ok lo, Ok hi -> Some (lo, hi)
                | _ -> None)
        in
        Option.bind bounds ~f:(fun (lo, hi) ->
            match position_of_offset lo, position_of_offset hi with
            | Some lo, Some hi -> Some (lo, hi)
            | _ -> None))
  | _ -> []

let int64_pair_of (lo : Cbat_word.t) (hi : Cbat_word.t)
    : (int64 * int64) option =
  match Cbat_word.to_int64 lo, Cbat_word.to_int64 hi with
  | Ok lo, Ok hi -> Some (lo, hi)
  | _ -> None

(* Split over ABSOLUTE positions: entirely at/above the entry RSP ->
   Caller; entirely below -> Range; otherwise Mixed.  The unbounded
   span names no side of the entry line, so it keeps itself. *)
let caller_split (k : kind) : kind =
  let cmp = Stdlib.Int64.compare in
  let ordered lo hi = cmp lo hi <= 0 in
  let entry = stack_base in
  match k with
  | Range (lo, hi) | Infinite (lo, hi) when not (is_unbounded_span lo hi) ->
    if ordered lo hi && cmp lo entry >= 0 then Caller (lo, hi)
    else if ordered lo hi && cmp hi entry <= 0 then k
    else Mixed (lo, hi)
  | k -> k

let classify (t : t) : kind =
  if is_top t then unbounded_span
  else
    let bounds =
      match offset_extrema t with
      | Some (lo, hi) ->
        Base.Option.bind (int64_pair_of lo hi) ~f:(fun (lo, hi) ->
            Base.Option.bind (position_of_offset lo) ~f:(fun lo ->
                Base.Option.map (position_of_offset hi) ~f:(fun hi -> (lo, hi))))
      | None ->
        (match min_elem t, max_elem t with
         | Some lo, Some hi -> int64_pair_of lo hi
         | _ -> None)
    in
    match bounds with
    | Some (lo, hi) ->
      let is_inf = is_infinite t || Stdlib.Int64.compare lo hi > 0 in
      if is_inf then Infinite (lo, hi) else Range (lo, hi)
    | None -> unbounded_span

(* The elements, when the set is enumerable within [cap]; [None] = the
   base is symbolic or the count exceeds the budget. *)
let enumerate ~(cap : int) (t : t) : word list option =
  if has_relative t then None else
#ifdef VSA_DEBUG
  if Cbat_word.gt_int (cardinality t) cap then begin
    let tag = match t with
      | Clp _ -> "Clp" | FinSet _ -> "FinSet" | Rel _ -> "Rel"
      | Many ps -> sprintf "Many%d" (List.length ps) in
    Printf.eprintf "hike-dbg-enum: cap=%d card=%s tag=%s\n%!"
      cap (Cbat_word.to_string (cardinality t)) tag;
    None
  end else
#else
  if Cbat_word.gt_int (cardinality t) cap then None else
#endif
    Some (iter t)

#ifdef VSA_DEBUG
(* The value's constructor, for the churn diagnosis. *)
let tag (t : t) : string =
  match t with
  | Clp _ -> "Clp"
  | FinSet _ -> "FinSet"
  | Rel _ -> "Rel"
  | Many ps -> sprintf "Many%d" (List.length ps)
#endif
