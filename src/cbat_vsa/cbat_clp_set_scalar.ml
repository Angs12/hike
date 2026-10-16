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
module Exact = Clp.Exact
module Origin = Hike_origin
module Origin_map = Map.Make (Origin)

type clp = Clp.t
type word = Cbat_word.t
type fset = Exact.t

(* Large sets are one Clp piece union; small ones exact run lists; relative
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
  | Exact of Exact.t
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

(* ---------------- leaf views (total over [Many]) ---------------- *)

let rec bitwidth (t : t) : int =
  match t with
  | Rel (_, _) -> 64
  | Clp ps -> P.bitwidth ps
  | Exact s -> Exact.bitwidth s
  | Many ps -> List.fold ps ~init:0 ~f:(fun a q -> Stdlib.max a (bitwidth q))

let rec is_bottom (t : t) : bool =
  match t with
  | Clp ps | Rel (_, ps) -> P.is_bottom ps
  | Exact s -> Exact.is_bottom s
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

(* The circular hull of a piece union: one piece, or the two arcs of one
   across the modulus; empty when the union is. *)
let hull_of_pieces (ps : P.t) : P.t option =
  let h = P.circular_hull ps in
  if P.is_bottom h then None else Some h

let hull_or_bottom (ps : P.t) : P.t = P.circular_hull ps

let pieces_of_finset (s : fset) : P.t = Exact.pieces s

(* The circular hull of a finite set. *)
let hull_of_finset fs : P.t =
  let width = Exact.bitwidth fs in
  match Exact.iter fs with
  | [] -> P.bottom width
  | [ x ] -> P.singleton x
  | l -> P.hull_of_list ~width l

(* ---------------- constructors ---------------- *)

let stack_word (offs : P.t) : t = Rel (Origin.Stack, offs)

let stack_word_i64 (k : int64) : t =
  Rel (Origin.Stack, P.singleton (Cbat_word.of_int64 k))

(* A module address: its link-time word in its section; an address
   outside every section stays a plain word. *)
let module_address (a : int64) : t =
  match Origin.Regions.of_address a with
  | Some r -> Rel (Origin.Rip r, P.singleton (Cbat_word.of_int64 a))
  | None -> Exact (Exact.singleton (Cbat_word.of_int64 a))

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

let checked_add (a : int64) (b : int64) : int64 option = checked_add3 a 0L b

(* Origins whose offsets are absolute words: plain values and module
   addresses, whose anchor records provenance, not an unknown base. *)
let absolute_line (o : Origin.t) : bool =
  match o with
  | Origin.Abs | Origin.Rip _ -> true
  | Origin.Stack | Origin.Fs -> false

(* The exact hull [base + offs_lo, base + offs_hi]; a missing
   direction clamps to the origin's materialisation bound — a
   relative claim stays in its origin's extent. *)
let plain_bounds (o : Origin.t) (offs : P.t) : (int64 * int64) option =
  if Origin.equal o Origin.Fs then None else
  let f = Origin.facts o in
  let floor = Stdlib.Int64.add f.Origin.base f.Origin.lo in
  let ceil = Stdlib.Int64.add f.Origin.base f.Origin.hi in
  let side w =
    Option.bind (Cbat_word.to_int64_opt w)
      ~f:(fun v -> checked_add f.Origin.base v) in
  let lo = match P.min_elem offs with
    | Some w -> side w
    | None -> Some floor in
  let hi = match P.max_elem offs with
    | Some w -> side w
    | None -> Some ceil in
  match lo, hi with
  | Some lo, Some hi when Stdlib.Int64.compare hi lo >= 0 -> Some (lo, hi)
  | _ -> None

(* The offsets' SIGNED extrema of a stack value (the offset line is
   signed: negative below the entry).  Exact over the arcs of every
   progression — offsets across the modulus measure instead of failing. *)
let offsets_signed_extrema (offs : P.t)
    : (Cbat_word.t * Cbat_word.t) option =
  let fold (acc : (Cbat_word.t * Cbat_word.t) option)
      (p : Clp.t) : (Cbat_word.t * Cbat_word.t) option =
    match Clp.min_elem_signed p, Clp.max_elem_signed p with
    | Some lo, Some hi ->
      (match acc with
       | None -> Some (lo, hi)
       | Some (alo, ahi) ->
         Some (Cbat_word.min_by ~signed:true lo alo,
               Cbat_word.max_by ~signed:true hi ahi))
    | _ -> acc
  in
  List.fold (P.to_list offs) ~init:None ~f:fold

(* The step-1 piece over the int64 position range [lo, hi]. *)
let line_interval (lo : int64) (hi : int64) : P.t =
  Clp.interval ~width:64 (Cbat_word.of_int64 lo) (Cbat_word.of_int64 hi)

(* ---------------- the tier census ---------------- *)

(* A live plain piece union under the small tier: kept unless it is
   small enough to become its exact twin.  [Pieces] already caps its
   results (the budget rule keeps a small exact union uncapped), so no
   tier cap is needed here. *)
let small_tier (cps : P.t) : t =
  if P.is_top cps || P.card_exceeds Utils.fin_set_size cps then Clp cps
  else Exact (Exact.of_pieces ~width:(P.bitwidth cps) cps)

(* A relative value's plain twin: the exact hull as a step-1 piece. *)
let rec to_plain (t : t) : t =
  match t with
  | Rel (o, offs) when absolute_line o -> Clp offs
  | Rel (o, offs) ->
    (match plain_bounds o offs with
     | Some (cmin, cmax)
       when Stdlib.Int64.compare cmin 0L >= 0
            && Stdlib.Int64.compare cmax cmin >= 0 ->
       Clp (line_interval cmin cmax)
     | _ -> Clp (P.top 64))
  | Many ps ->
    (match canonical (List.map ps ~f:to_plain) with
     | Clp _ | Exact _ | Rel _ as q -> q
     | Many ps' -> Many ps')
  | Clp _ | Exact _ -> t

(* ---------------- canonicalization ---------------- *)

(* The canonical value: one leaf, or [Many] of the canonical leaf list
   in the fixed order Clp, Exact, Rel (no nesting); bottoms drop
   (an all-bottom value keeps one empty Exact so the width survives);
   an over-budget Exact pool promotes to its exact piece runs; a lone
   small plain piece union keeps its exact small-tier twin (the tier).
   The relative pool groups by origin: a pool of two or more origins
   is not a value — its members materialise into the plain pool. *)
and canonical (ps : t list) : t =
  let budget = Utils.fin_set_size in
  (* A lone leaf takes the pool rules' answer directly: a relative leaf is
     itself; a live Clp stays unless the small tier takes it; a live
     Exact stays unless it promotes to its pieces. *)
  match ps with
  | [ (Rel _ as q) ] -> q
  | [ (Clp x as q) ] when not (P.is_bottom x) ->
    if P.is_top x || P.card_exceeds budget x then q else small_tier x
  | [ (Exact s as q) ] when not (Exact.is_bottom s) ->
    if Exact.card_exceeds budget s then small_tier (pieces_of_finset s) else q
  | _ -> canonical_pool ps

and canonical_pool (ps : t list) : t =
  let alive = List.filter ps ~f:(fun q -> not (is_bottom q)) in
  let max_width = List.fold ps ~init:1 ~f:(fun a q -> Stdlib.max a (bitwidth q)) in
  (* One relative leaf per origin, in origin order: a union keeps every
     origin it was built from.  One merge is lossless and keeps the form
     canonical: an absolute leaf's offsets are its words (the plain
     pool). *)
  let abs_rev, rel_pool =
    List.fold ps ~init:([], Origin_map.empty) ~f:(fun (abs, rels) -> function
        | Rel (Origin.Abs, x) -> x :: abs, rels
        | Rel (o, x) ->
          abs,
          Map.update rels o ~f:(function
              | None -> x
              | Some prior -> P.union prior x)
        | _ -> abs, rels) in
  let so_pool = Map.to_alist rel_pool in
  let mixed_pool = List.rev abs_rev in
  (match alive, so_pool with
  | [], (o, offs) :: _ ->
    (* The symbolic bottom keeps its origin: an empty offset set is
       still a relative value (its consumers span the full key line). *)
    Rel (o, offs)
  | [], [] ->
    Exact (Exact.bottom max_width)
  | _ ->
    let clps =
      List.append mixed_pool
        (List.filter_map alive ~f:(function Clp x -> Some x | _ -> None))
    in
    let fss =
      List.filter_map alive ~f:(function Exact x -> Some x | _ -> None) in
    let promote =
      match fss with
      | [] -> false
      | [ s ] -> Exact.card_exceeds Utils.fin_set_size s
      | _ ->
        List.fold fss ~init:0 ~f:(fun a s ->
            let c = Exact.count s in
            if c > Stdlib.max_int - a then Stdlib.max_int else a + c)
        > Utils.fin_set_size
    in
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
        | x :: rest -> Some (List.fold rest ~init:x ~f:Exact.union)
    in
    (* Contained pieces drop: an Exact leaf covered by the Clp leaf adds
       no element, and a Clp leaf covered by the Exact is that Exact.
       Both would double-count the overlap in [cardinality].  A lone
       small Clp leaf then takes its exact twin. *)
    let clp_piece, fs_piece =
      match clp_piece, fs_piece with
      | Some cps, Some fss
        when List.for_all (Exact.iter fss) ~f:(fun w -> P.elem w cps) ->
        (Some cps, None)
      | Some cps, Some fss
        when (not (P.is_top cps))
             && not (P.card_exceeds Utils.fin_set_size cps)
             && List.for_all (P.elements cps) ~f:(fun w -> Exact.elem w fss)
        -> (None, Some fss)
      | c, f -> c, f
    in
    let clp_piece, fs_piece =
      match clp_piece, fs_piece with
      | Some cps, None
        when (not (P.is_bottom cps)) && not (P.is_top cps)
             && not (P.card_exceeds Utils.fin_set_size cps)
        -> None, Some (Exact.of_pieces ~width:(P.bitwidth cps) cps)
      | c, f -> c, f
    in
    (* A bottom relative leaf drops against live pieces. *)
    let rel_pieces =
      List.filter_map so_pool ~f:(fun (o, offs) ->
          if P.is_bottom offs then None else Some (Rel (o, offs)))
    in
    let leaves =
      List.filter_map
        [ Option.map clp_piece ~f:(fun x -> Clp x);
          Option.map fs_piece ~f:(fun x -> Exact x) ]
        ~f:(fun q -> q)
      @ rel_pieces
    in
    (match leaves with
     | [ q ] -> q
     | [] ->
       (* No leaf survived: a bottom at the widest input, never an empty
          [Many] (which would carry width 0). *)
       Exact (Exact.bottom max_width)
     | ps -> Many ps))


(* The plain twin: a symbolic piece materialized, a plain value as-is. *)
let plain_view (t : t) : t = match t with Rel _ -> to_plain t | q -> q

(* The value's runtime origin: [Some o] exactly when every piece of the
   value is relative to the one origin [o]; absolute, plain, and
   mixed-origin values are [None]. *)
let rec origin (t : t) : Origin.t option =
  match t with
  | Rel (o, _) -> Some o
  | Clp _ | Exact _ -> None
  | Many ps ->
    (match List.map ps ~f:origin with
     | (Some o) :: rest ->
       if
         List.for_all rest
           ~f:(function Some o' -> Origin.equal o o' | None -> false)
       then Some o
       else None
     | _ -> None)

(* Re-tags a relative value's origin, offsets unchanged. *)
let set_origin (o : Origin.t) (t : t) : t =
  match t with Rel (_, offs) -> Rel (o, offs) | q -> q

(* Plain-operand top test. *)
let rec plain_is_top (t : t) : bool =
  match t with
  | Clp ps -> P.is_top ps
  | Exact _ -> false
  | Rel (_, offs) -> P.is_top offs
  | Many ps -> List.exists ps ~f:plain_is_top

(* The circular hull of the whole plain value. *)
let as_hull (t : t) : P.t =
  match to_plain t with
  | Clp ps ->
    (match hull_of_pieces ps with
     | Some p -> p
     | None -> P.top (Stdlib.max 1 (P.bitwidth ps)))
  | Exact s -> hull_of_finset s
  | Many ps ->
    let hulls =
      List.filter_map ps ~f:(function
        | Exact s -> Some (hull_of_finset s)
        | Clp hps -> hull_of_pieces hps
        | Rel _ -> None
        | Many _ -> None)
    in
    (match hulls with
     | [] -> P.top 64
     | p :: rest -> List.fold rest ~init:p ~f:P.hull_union)
  | _ -> P.top 64

let of_list ~width l : t =
  canonical
    [ (if List.length l > Utils.fin_set_size then Clp (P.of_list ~width l)
       else Exact (Exact.of_list ~width l)) ]

let singleton w : t = Exact (Exact.singleton w)

let of_clp (ps : P.t) : t = canonical [ Clp ps ]

let of_exact (s : Exact.t) : t = canonical [ Exact s ]

let bottom i = Exact (Exact.bottom i)
(* Shared per width: env reads and writes build their default top. *)
let top_cache : t array =
  Array.init 257 ~f:(fun i -> canonical [ Clp (P.top (Int.max i 1)) ])

let top i =
  if i > 0 && i < Array.length top_cache then top_cache.(i)
  else canonical [ Clp (P.top i) ]

(* One leaf, or the [Many] pieces. *)
let leaves (t : t) : t list = match t with Many ps -> ps | q -> [ q ]

(* The pairwise leaf fan-out: [f] per leaf pair, canonically merged. *)
let pairwise (f : t -> t -> t list) (t1 : t) (t2 : t) : t =
  canonical
    (List.concat_map (leaves t1) ~f:(fun q1 ->
         List.concat_map (leaves t2) ~f:(fun q2 -> f q1 q2)))

(* ---------------- the kind-aligned leaf pairing ---------------- *)

(* The leaf of each plain kind: a canonical value carries at most one
   (the [canonical] fold collapses same-kind leaves), so the first match
   is the only one; it carries one relative leaf per origin. *)
let clp_leaf (t : t) : P.t option =
  match t with
  | Clp ps -> Some ps
  | Many ps -> List.find_map ps ~f:(function Clp x -> Some x | _ -> None)
  | Exact _ | Rel _ -> None

let fs_leaf (t : t) : fset option =
  match t with
  | Exact s -> Some s
  | Many ps -> List.find_map ps ~f:(function Exact x -> Some x | _ -> None)
  | Clp _ | Rel _ -> None

let rel_leaves (t : t) : (Origin.t * P.t) list =
  List.filter_map (leaves t) ~f:(function Rel (o, x) -> Some (o, x) | _ -> None)

(* The join pairing: every kind carried by EITHER side contributes — a
   shared kind takes its own join, a one-sided kind is carried (the join
   includes it).  Exact for the lattice join, which is why the join may
   carry where a widening may not. *)
let pair_join ~(clp_op : P.t -> P.t -> P.t) ~(fs_op : fset -> fset -> fset)
    (t1 : t) (t2 : t) : t =
  let parts =
    (match clp_leaf t1, clp_leaf t2 with
     | Some a, Some b -> [ Clp (clp_op a b) ]
     | Some a, None | None, Some a -> [ Clp a ]
     | None, None -> [])
    @ (match fs_leaf t1, fs_leaf t2 with
       | Some a, Some b -> [ Exact (fs_op a b) ]
       | Some a, None | None, Some a -> [ Exact a ]
       | None, None -> [])
    (* Every relative leaf of either side: the pool unions one origin's
       offsets and keeps the origins apart. *)
    @ List.map (rel_leaves t1 @ rel_leaves t2) ~f:(fun (o, x) -> Rel (o, x))
  in
  canonical parts

(* The concrete extrema of a set, before any stack projection. *)
let extrema (t : t) : (Cbat_word.t * Cbat_word.t) option =
  let leaf (q : t) : (Cbat_word.t * Cbat_word.t) option =
    let pair lo hi = Option.map2 lo hi ~f:(fun lo hi -> (lo, hi)) in
    match q with
    | Rel (o, offs) ->
      (match plain_bounds o offs with
       | Some (cmin, cmax) -> Some (Cbat_word.of_int64 cmin, Cbat_word.of_int64 cmax)
       | None -> None)
    | Clp ps -> pair (P.min_elem ps) (P.max_elem ps)
    | Exact s -> pair (Exact.min_elem s) (Exact.max_elem s)
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
         Some (Cbat_word.min_by ~signed:false lo alo,
               Cbat_word.max_by ~signed:false hi ahi))
  in
  go None t

(* Stack identity comes only from the carried runtime origin. *)
let in_stack_segment (t : t) : bool =
  Option.exists (origin t) ~f:Origin.names_stack_line

let rec cardinality (t : t) : word =
  match t with
  | Clp ps -> P.cardinality ps
  | Exact s -> Exact.cardinality s
  (* An absolute-origin value's offsets ARE its absolute words: the
     base is the fixed 0, no segment multiplies. *)
  | Rel ((Origin.Abs | Origin.Rip _), offs) -> P.cardinality offs
  | Rel (Origin.Stack, offs) -> stack_cardinality offs
  | Rel (Origin.Fs, offs) ->
    if P.is_bottom offs then Cbat_word.zero 65
    else Cbat_word.lshift (Cbat_word.one 65) (Cbat_word.of_int ~width:65 64)
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
    | q -> Cbat_word.keep_better ~better acc (leaf q)
  in
  go None t

(* One leaf's unsigned lower or upper bound. *)
let leaf_bound ~(lower : bool) (q : t) : word option =
  match q with
  | Rel (o, offs) when absolute_line o ->
    if lower then P.min_elem offs else P.max_elem offs
  | Rel (o, offs) ->
    Option.map (plain_bounds o offs) ~f:(fun (cmin, cmax) ->
        Cbat_word.of_int64 (if lower then cmin else cmax))
  | Clp ps -> if lower then P.min_elem ps else P.max_elem ps
  | Exact s -> if lower then Exact.min_elem s else Exact.max_elem s
  | Many _ -> None

let rec has_fs = function
  | Rel (Origin.Fs, _) -> true
  | Many ps -> List.exists ps ~f:has_fs
  | _ -> false

let min_elem (t : t) : word option =
  if has_fs t then None else
    extremum (leaf_bound ~lower:true) (Cbat_word.min_by ~signed:false) t

let max_elem (t : t) : word option =
  if has_fs t then None else
    extremum (leaf_bound ~lower:false) (Cbat_word.max_by ~signed:false) t

(* Stack-family extrema on the entry-relative offset line. *)
let offset_extrema (t : t) : (Cbat_word.t * Cbat_word.t) option =
  match t with
  | Rel (o, offs) when Origin.names_stack_line o -> offsets_signed_extrema offs
  | _ -> None

let stack_bounds (t : t) : (int64 * int64) option =
  (* Stack-origin extrema on the offset line. *)
  Option.bind (offset_extrema t) ~f:(fun (lo, hi) -> Cbat_word.int64_pair lo hi)


let signed_better ~(dir : int) : Cbat_word.t -> Cbat_word.t -> Cbat_word.t =
  if dir < 0 then Cbat_word.min_by ~signed:true
  else Cbat_word.max_by ~signed:true

(* The signed extreme of one leaf; [dir] < 0 is the minimum, > 0 the
   maximum.  A sign-spanning piece has no signed extreme on that side;
   a signed-positive projection's signed and unsigned extrema agree. *)
let signed_leaf ~(dir : int) (q : t) : word option =
  let pick (a, b) = if dir < 0 then a else b in
  let clamp = if dir < 0 then Stdlib.Int64.min_int else Stdlib.Int64.max_int in
  let better = signed_better ~dir in
  let via_offsets_base base offs =
    Option.bind (offsets_signed_extrema offs)
      ~f:(fun ex ->
        Option.bind (checked_add base
                       (Option.value (Cbat_word.to_int64_opt (pick ex))
                          ~default:clamp))
          ~f:(fun v -> Some (Cbat_word.of_int64 v)))
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
        Cbat_word.keep_better ~better acc r)
  in
  match q with
  | Rel (Origin.Fs, _) -> None
  | Rel (o, offs) -> via_offsets_base (Origin.facts o).base offs
  | Clp ps -> via_pieces ps
  | Exact s ->
    (if dir < 0 then Exact.min_elem_signed s else Exact.max_elem_signed s)
  | Many _ -> None

let extremum_signed ~(dir : int) (t : t) : word option =
  if has_fs t then None else extremum (signed_leaf ~dir) (signed_better ~dir) t

let min_elem_signed (t : t) : word option = extremum_signed ~dir:(-1) t
let max_elem_signed (t : t) : word option = extremum_signed ~dir:1 t

(* Offset space: the per-sub cell-key universe keys by offsets. *)
let rec splits_by (t : t) (w : Cbat_word.t) =
  match t with
  | Clp offs | Rel (_, offs) -> P.splits_by offs w
  | Exact s -> Exact.splits_by s w
  | Many ps -> List.for_all ps ~f:(fun q -> splits_by q w)

(* Hull test: an over-approximation of membership in the projection. *)
let rec elem w (t : t) =
  match t with
  | Rel (o, offs) when absolute_line o -> P.elem w offs
  | Rel (o, offs) ->
    (match plain_bounds o offs with
     | Some (cmin, cmax) ->
       (match Cbat_word.to_int64_opt w with
        | Some wi ->
          Stdlib.Int64.compare wi cmin >= 0
          && Stdlib.Int64.compare wi cmax <= 0
        | None -> false)
     | None -> not (is_bottom t))
  | Clp ps ->
    (* [P.elem] asserts equal widths; a mismatched query is not a member. *)
    Cbat_word.bitwidth w = P.bitwidth ps && P.elem w ps
  | Exact s -> Exact.elem w s
  | Many ps -> List.exists ps ~f:(fun q -> elem w q)

(* Materializes the base-0 slice only; the full projection is
   8 MiB of elements. *)
let rec iter (t : t) : word list =
  match t with
  | Rel (Origin.Fs, _) -> invalid_arg "WordSet.iter: a symbolic FS base is not enumerable"
  (* An absolute-line value enumerates its offsets as they are. *)
  | Rel (o, offs) when absolute_line o -> P.elements offs
  | Rel (o, offs) ->
    List.map (P.elements offs)
      ~f:(fun w -> Cbat_word.add (Cbat_word.of_int64 (Origin.facts o).base) w)
  | Clp ps -> P.elements ps
  | Exact s -> Exact.iter s
  | Many ps -> List.concat_map ps ~f:iter

(* The fixpoint's convergence check calls this on every var of every
   visit: the leaf arms avoid the derived compare's list machinery. *)
let rec equal (t1 : t) (t2 : t) : bool =
  phys_equal t1 t2 ||
  match t1, t2 with
  | Clp a, Clp b -> P.equal a b
  | Exact a, Exact b -> Exact.equal a b
  | Rel (o1, a), Rel (o2, b) -> Origin.equal o1 o2 && P.equal a b
  | Many a, Many b ->
    List.length a = List.length b
    && List.for_all2_exn a b ~f:equal
  | _ -> false

let overlap (t1 : t) (t2 : t) : bool =
  (* The hull's width; an empty hull reads as one bit wide. *)
  let hull_width h = if P.is_bottom h then 1 else P.bitwidth h in
  let leaf_pair q1 q2 =
    match q1, q2 with
    | Exact s1, Exact s2 -> Exact.overlap s1 s2
    | Exact s1, Clp ps2 ->
      let h = hull_or_bottom ps2 in
      Exact.overlap_elem ~width:(hull_width h) ~elem:(fun w -> P.elem w h) s1
    | Clp ps1, Exact s2 ->
      let h = hull_or_bottom ps1 in
      Exact.overlap_elem ~width:(hull_width h) ~elem:(fun w -> P.elem w h) s2
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

(* Collapse a piece-union result to one progression: the distributed
   arithmetic policy, since multi-piece results churn the fixpoint (the
   piece cap is not associative under repeated joins, and in-loop values
   oscillate between incomparable capped forms).  The interior exclusion
   a piece union can hold is lost here, not at the join. *)
let piece_collapse (ps : P.t) : P.t =
  match P.to_list ps with
  | [ _ ] -> ps
  | _ ->
    match hull_of_pieces ps with
    | Some h -> h
    | None -> ps

(* The pairwise product stays within [max_pieces] pairs: past it, the
   wider operand enters as its hull (sound). *)
let binop_pieces (op : binop) (a : P.t) (b : P.t) : P.t =
  let na = List.length (P.to_list a) and nb = List.length (P.to_list b) in
  let a, b =
    if na * nb <= Utils.max_pieces then (a, b)
    else if na >= nb then (piece_collapse a, b)
    else (a, piece_collapse b) in
  Piece_binop.binop op a b

module Fs_repr = struct
  type t = fset

  let union = Exact.union
  let meet = Exact.intersection
  let add = Exact.add
  let sub = Exact.sub
  let mul = Exact.mul
  let div = Exact.div
  let sdiv = Exact.sdiv
  let modulo = Exact.modulo
  let smodulo = Exact.smodulo
  let lshift = Exact.lshift
  let rshift = Exact.rshift
  let arshift = Exact.arshift
  let logand = Exact.logand
  let logor = Exact.logor
  let logxor = Exact.logxor
  let concat = Exact.concat
end

module Fs_binop = Binop (Fs_repr)

let binop_fs (op : binop) (s1 : fset) (s2 : fset) : fset =
  Fs_binop.binop op s1 s2

(* One op over one leaf pair.  The representation pair decides the path;
   the paths are named so the dispatcher reads as a table. *)
type repr =
  | Fs of fset
  | Ps of P.t
  | Opaque

let repr_of (q : t) : repr =
  match q with
  | Exact s -> Fs s
  | Clp ps -> Ps ps
  | Rel _ | Many _ -> Opaque

(* Both leaves exact: the element product. *)
let op_fs_fs (op : binop) (s1 : fset) (s2 : fset) : t =
  Exact (binop_fs op s1 s2)

(* Both leaves plain: the piece union on each side. *)
let op_ps_ps (op : binop) (a : P.t) (b : P.t) : t =
  Clp (binop_pieces op a b)

(* Mixed: the exact side becomes the piece union of its elements at the
   declared width, the operands in their own order. *)
let op_ps_fs (op : binop) (a : P.t) (s : fset) : t =
  Clp (binop_pieces op a (pieces_of_finset s))

let op_fs_ps (op : binop) (s : fset) (b : P.t) : t =
  Clp (binop_pieces op (pieces_of_finset s) b)

(* A relative/opaque leaf is top at the wider width. *)
let op_wide (q1 : t) (q2 : t) : t =
  Clp (P.top (Stdlib.max (bitwidth q1) (bitwidth q2)))

(* The dispatcher: one row per representation pair. *)
let op_pair (op : binop) (q1 : t) (q2 : t) : t list =
  match repr_of q1, repr_of q2 with
  | Fs s1, Fs s2 -> [ op_fs_fs op s1 s2 ]
  | Ps a, Ps b -> [ op_ps_ps op a b ]
  | Ps a, Fs s -> [ op_ps_fs op a s ]
  | Fs s, Ps b -> [ op_fs_ps op s b ]
  | Opaque, _ | _, Opaque -> [ op_wide q1 q2 ]

let lift_binop (op : binop) (t1 : t) (t2 : t) : t =
  match to_plain t1, to_plain t2 with
  | ((Clp _ | Exact _ | Rel _) as q1), ((Clp _ | Exact _ | Rel _) as q2) ->
    canonical (op_pair op q1 q2)
  | p1, p2 -> pairwise (op_pair op) p1 p2

let rec lift_unop (f_clp : P.t -> P.t) (f_fs : fset -> fset) : t -> t = fun t ->
  match t with
  | Clp ps -> canonical [ Clp (f_clp ps) ]
  | Exact s -> canonical [ Exact (f_fs s) ]
  | Rel _ as q ->
    (match to_plain q with
     | Clp ps -> canonical [ Clp (f_clp ps) ]
     | Exact s -> canonical [ Exact (f_fs s) ]
     | Rel _ | Many _ -> t)
  | Many ps -> canonical (List.map ps ~f:(fun q -> lift_unop f_clp f_fs q))

(* ---------------- stack queries ---------------- *)

(* The offset piece union of a stack-symbolic value — answers ONLY for
   the symbolic arm; a plain in-band set is None.  The single-progression
   view is the hull (the exact union is the piece list itself). *)
let stack_offsets (t : t) : P.t option =
  match t with
  | Rel (o, offs) when Origin.names_stack_line o ->
    Some (hull_or_bottom offs)
  | _ -> None

let relative_offsets (t : t) : P.t option =
  match t with Rel (_, offs) -> Some offs | _ -> None

(* The stack-line leaves of a value (itself when it is one): the stack
   addresses the value may hold, one leaf per stack-line origin. *)
let stack_leaves (t : t) : t list =
  List.filter (leaves t) ~f:(function Rel (o, _) -> Origin.names_stack_line o | _ -> false)

(* The memory-key coordinate line.  A module address names the same
   bytes as its absolute word, so [Rip] keys on the [Abs] line.  The
   origin still rides the value; only the key line is coarsened. *)
let key_line (o : Origin.t) : Origin.t =
  match o with
  | Origin.Stack | Origin.Fs -> o
  | Origin.Rip _ | Origin.Abs -> Origin.Abs

(* Memory keys retain the carried origin's line; plain values stay
   absolute.  A mixed value names each leaf's line: its addresses are
   the union of its leaves'. *)
let rec address_groups (t : t) : (Origin.t * P.t) list =
  match t with
  | Rel (o, offs) -> [ (key_line o, offs) ]
  | Clp ps -> [ (Origin.Abs, ps) ]
  | Exact s -> [ (Origin.Abs, pieces_of_finset s) ]
  | Many ps -> List.concat_map ps ~f:address_groups

(* A finite progression split at its value midpoint; a singleton has no
   halves. *)
let halves (p : clp) : (clp * clp) option =
  match Clp.min_elem p, Clp.max_elem p with
  | Some lo, Some hi when Cbat_word.(<) lo hi ->
    let one = Cbat_word.one (Cbat_word.bitwidth lo) in
    Some (Clp.split_at_n p (Cbat_word.add lo (Cbat_word.rshift (Cbat_word.sub hi lo) one)))
  | _ -> None

(* The elements of [t] [decide] keeps, bisected per progression on its
   memory key line: [decide line p] keeps or drops a whole
   sub-progression [p], splits it, or partitions it ([`Parts`] applies
   the listed verdicts without recursion — the pieces replace [p]); a
   singleton never splits, and an undecided one stays.  The origin is
   kept.  An unbounded piece and a mixed-origin value are kept
   whole. *)
type address_verdict =
  [ `Keep | `Drop | `Split | `Parts of (clp * [ `Keep | `Drop ]) list ]

let filter_addresses (t : t)
    ~(decide : Origin.t -> clp -> address_verdict) : t =
  (* Visit the upper half first so consing preserves ascending order. *)
  let rec bisect line acc (p : clp) =
    match decide line p with
    | `Keep -> p :: acc
    | `Drop -> acc
    | `Split ->
      (match halves p with
       | Some (a, b) -> bisect line (bisect line acc b) a
       | None -> p :: acc)
    | `Parts parts ->
      List.fold_right parts ~init:acc ~f:(fun (q, verdict) acc ->
          match verdict with `Keep -> q :: acc | `Drop -> acc) in
  let filter line (ps : P.t) : P.t option =
    let progs = P.to_list ps in
    if List.exists progs ~f:Clp.is_infinite then None
    else
      let kept =
        (* Source grids can interleave; merge their survivor streams. *)
        List.map progs ~f:(bisect line [])
        |> Utils.merge_balanced ~merge:P.merge_progressions in
      Some (P.of_progressions kept) in
  match t with
  | Many _ -> t
  | Rel (o, ps) ->
    Option.value_map (filter (key_line o) ps) ~default:t ~f:(fun ps -> Rel (o, ps))
  | Clp ps ->
    Option.value_map (filter Origin.Abs ps) ~default:t ~f:(fun ps -> canonical [ Clp ps ])
  | Exact s ->
    let kept =
      Exact.filter s ~f:(fun w ->
          match decide Origin.Abs (Clp.singleton w) with
          | `Drop -> false
          | `Keep | `Split -> true
          | `Parts parts ->
            List.exists parts ~f:(fun (q, verdict) ->
                match verdict with `Keep -> Clp.elem w q | `Drop -> false)) in
    if phys_equal kept s then t else Exact kept

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
          (match Cbat_word.to_int64_opt s with
           | Some i
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
    | Exact s ->
      (match Exact.iter s with
       | [] | [ _ ] -> Some 1
       | _ :: rest as ws ->
         let diffs =
           List.map2_exn (List.drop_last_exn ws) rest
             ~f:(fun a b -> Cbat_word.sub b a) in
         (match List.all_equal diffs ~equal:Cbat_word.equal with
          | Some d when not (Cbat_word.is_zero d) ->
            (match Cbat_word.to_int64_opt d with
             | Some i -> Some (Stdlib.max 1 (Stdlib.Int64.to_int i))
             | None -> Some 1)
          | _ -> Some 1))
    | Many _ -> None
  in
  match t with
  | Many ps ->
    (match
       List.all_equal (List.map ps ~f:leaf_stride)
         ~equal:(Option.equal Int.equal)
     with
     | Some (Some s) -> s
     | _ -> 1)
  | q -> Option.value (leaf_stride q) ~default:1

let origin_is_relative x = not (absolute_line x)

(* THE per-op type table: what [op] yields when its operands meet at
   origins [o1] and [o2] (an absolute operand is [Origin.Abs]).
   [Wrap o] = the offsets stay relative at [o]; [Materialise] = the
   bases do not survive — both hulls, the plain op; [Top] = the op
   keeps unknown base bits: top.  THE table is the one home of "what
   type dominates"; a new origin lands by extending [Origin.t], a new
   op by one row here. *)
let rel_table (op : binop) (o1 : Origin.t) (o2 : Origin.t) :
    Hike_origin.rel_row =
  let rel x = origin_is_relative x in
  match op with
  (* [lift2] answers a union before the table (the join keeps one leaf
     per origin); its row is the same-origin one. *)
  | Union ->
    if rel o1 && rel o2 && Origin.equal o1 o2 then Wrap o1 else Materialise
  | Meet ->
    if rel o1 && rel o2 then
      if Origin.equal o1 o2 then Wrap o1 else Materialise
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
  | Logand | Logor | Logxor ->
    if rel o1 && rel o2 then Top
    else if rel o1 then Wrap o1
    else if rel o2 then Wrap o2
    else Materialise
  | Mul | Div | Sdiv | Modulo | Smodulo
  | Lshift | Rshift | Arshift | Concat ->
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
  | Exact s ->
    Some
      (Exact.pieces
         (Exact.of_iter ~width:64 ~iter:(fun emit ->
              List.iter (Exact.iter s) ~f:(fun w ->
                  emit (Cbat_word.sub w base)))))
  | _ -> None


(* The singleton word of a plain operand, if it is one. *)
let singleton_of (q : t) : word option =
  let pair a b = if Cbat_word.equal a b then Some a else None in
  match q with
  | Clp ps ->
    (match P.min_elem ps, P.max_elem ps with
     | Some a, Some b -> pair a b
     | _ -> None)
  | Exact s ->
    (match Exact.min_elem s, Exact.max_elem s with
     | Some a, Some b -> pair a b
     | _ -> None)
  | Rel _ | Many _ -> None


(* [f] over the offsets while enumerable; top past the budget. *)
let certified_image ~(origin : Origin.t) ~(width : int) (f : word -> word) (offs : P.t) : t =
  let base = Cbat_word.of_int64 ((Origin.facts origin).base) in
  match Cbat_word.to_int (P.cardinality offs) with
  | Ok n when n > 0 && n <= Utils.fin_set_size ->
    of_list ~width
      (List.map (P.elements offs)
         ~f:(fun o ->
             Cbat_word.cast Bil.UNSIGNED width (f (Cbat_word.add base o))))
  | _ -> top width

(* [f]'s OFFSET image on the origin's own line: a bit op confined to the
   certified bits changes each base+offset by an amount fixed by its
   residue mod 2^certified, so the result stays on the line.  Enumerable
   offsets map exactly; a non-enumerable set unions the translates of
   every residue's change (sound — the change depends only on
   o mod 2^certified). *)
let certified_offset_image (origin : Origin.t) (f : word -> word) (offs : P.t) :
    P.t option =
  let facts = Origin.facts origin in
  let base = Cbat_word.of_int64 facts.base in
  let c = facts.certified in
  if c <= 0 || c >= 64 then None
  else
    let change_off o =
      let x = Cbat_word.add base o in
      Cbat_word.add o (Cbat_word.sub (f x) x) in
    match Cbat_word.to_int (P.cardinality offs) with
    | Ok n when n > 0 && n <= Utils.fin_set_size ->
      Some
        (Exact.pieces
           (Exact.of_iter ~width:64 ~iter:(fun emit ->
                P.iter offs ~f:(fun p ->
                    List.iter (Clp.iter p) ~f:(fun o -> emit (change_off o))))))
    | _ ->
      let delta r =
        let x = Cbat_word.add base (Cbat_word.of_int64 (Int64.of_int r)) in
        Cbat_word.sub (f x) x in
      Some
        (List.fold (List.init (1 lsl c) ~f:delta) ~init:(P.bottom 64)
           ~f:(fun acc d -> P.union acc (P.translate offs d)))


(* The round-down mask class: [k = ~m] with [m = 2^s - 1] (all-ones is
   s = 64, the identity).  The shift the mask implies, if [k] is one. *)
let round_down_shift (k : word) : int option =
  if Cbat_word.equal k (Cbat_word.ones 64) then Some 64
  else
    let m = Cbat_word.sub (Cbat_word.ones 64) k in
    let m1 = Cbat_word.add m (Cbat_word.one 64) in
    if Cbat_word.is_zero m1 then None
    else if Cbat_word.is_zero (Cbat_word.logand m m1) then
      Some (match Cbat_word.lead_1_bit m with None -> 0 | Some b -> b + 1)
    else None

(* Round offsets using the carried base's certified residue. *)
let round_down_image_for (o : Origin.t) (s : int) (offs : P.t) : P.t option =
  if s >= 64 then Some offs
  else
  let facts = Origin.facts o in
  if s > facts.certified then
    let slack = Cbat_word.sub (Cbat_word.lshift (Cbat_word.one 64)
        (Cbat_word.of_int ~width:64 s)) (Cbat_word.one 64) in
    Some (P.sub offs (Clp.interval ~width:64 (Cbat_word.zero 64) slack))
  else
    let m64 = Stdlib.Int64.pred (Stdlib.Int64.shift_left 1L s) in
    let b_lo = Stdlib.Int64.logand facts.base m64 in
    let block (w : word) =
      match Cbat_word.to_int64 w with
      | Error _ -> None
      | Ok v ->
        let r = Stdlib.Int64.logand (Stdlib.Int64.add b_lo v) m64 in
        Some (Cbat_word.of_int64 ~width:64 (Stdlib.Int64.sub v r))
    in
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
                Some (P.of_arcs (Clp.arcs a' ~step ~cardn:cnt))
              | _ -> None)
          | _ -> None)
    in
    let rec union_all = function
      | [] -> P.bottom 64
      | [ g ] -> g
      | g :: rest -> P.union g (union_all rest)
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
    | Exact s1, Exact s2 -> [ Exact (Exact.intersection s1 s2) ]
    | Exact s, Clp ps | Clp ps, Exact s ->
      [ Exact (Exact.filter s ~f:(fun w -> P.elem w ps)) ]
    | Clp ps1, Clp ps2 -> [ Clp (P.intersection ps1 ps2) ]
    | _ -> []
  in
  pairwise pair t1 t2

(* The plain join: every leaf pair contributes — two Clp leaves the exact
   piece union, two Exact leaves the exact union, a one-sided kind its
   own leaf — so the join never hulls. *)
let join_plain (t1 : t) (t2 : t) : t =
  pair_join ~clp_op:P.union ~fs_op:Exact.union t1 t2

(* The [Materialise] payload: both hulls, the plain op; [Sub]'s
   relative-relative row keeps the exact offset difference (the base
   cancels — no collapse).  Two stack-line origins meet on the Stack
   line: materialising a stack address would move it off the stack key
   line. *)
let materialise2 (op : binop) (t1 : t) (t2 : t) : t =
  match op, t1, t2 with
  | Meet, _, _ when has_fs t1 || has_fs t2 -> join_plain t1 t2
  | Sub, Rel (o1, a), Rel (o2, b) when Origin.equal o1 o2 ->
    canonical [ Clp (P.sub a b) ]
  | Meet, Rel (o1, a), Rel (o2, b)
    when Origin.names_stack_line o1 && Origin.names_stack_line o2 ->
    canonical [ Rel (Origin.Stack, P.intersection a b) ]
  | _ -> lift_binop op (to_plain t1) (to_plain t2)

(* The plain-plain payload: the lattice ops pair by kind; every other op
   lifts through the common plain machinery. *)
let generic (op : binop) (t1 : t) (t2 : t) : t =
  match op with
  | Meet -> meet_plain t1 t2
  | Union -> join_plain t1 t2
  | _ -> lift_binop op t1 t2

(* A relative value met with a plain constraint: the constraint's words
   translate into the offsets on the fixed base. *)
let meet_rel (t1 : t) (t2 : t) : t =
  let meet_offs o a plain =
    if Origin.equal o Origin.Fs then
      if is_bottom plain then bottom 64 else Rel (o, a)
    else
    match plain_offsets o plain with
    | Some o2 -> canonical [ Rel (o, P.intersection a o2) ]
    | None -> canonical [ Rel (o, P.bottom 64) ]
  in
  match t1, t2 with
  | Rel (o, a), (Clp _ | Exact _ as plain) -> meet_offs o a plain
  | (Clp _ | Exact _ as plain), Rel (o, a) -> meet_offs o a plain
  | _ -> meet_plain (to_plain t1) (to_plain t2)

let logand_rel (o : Origin.t) (offs : P.t) (plain : t) : t =
  let certified_bits = (Origin.facts o).certified in
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

(* OR/XOR with a constant below the certified bits: the result stays a
   stack-line relative value with a residue-dependent offset map (the
   identity for k = 0).  Any other constant (or a non-constant) answers
   top — the uncertified base bits would leak. *)
let logor_rel_xor (op : binop) (o : Origin.t) (offs : P.t) (plain : t) : t =
  let certified_bits = (Origin.facts o).certified in
  match singleton_of plain with
  | Some k when Cbat_word.is_zero k -> canonical [ Rel (o, offs) ]
  | Some k
    when certified_bits >= 64
         || (certified_bits > 0
             && Cbat_word.leq_int k ((1 lsl certified_bits) - 1)) ->
    let k64 = Cbat_word.cast Bil.UNSIGNED 64 k in
    let f v = match op with Logor -> Cbat_word.logor v k64 | _ -> Cbat_word.logxor v k64 in
    (match certified_offset_image o f offs with
     | Some offs' -> canonical [ Rel (o, offs') ]
     | None -> top 64)
  | _ -> top 64

let rel_abs (op : binop) (t1 : t) (t2 : t) : t =
  match op with
  | Add | Sub ->
    let f = match op with Sub -> P.hull_sub | _ -> P.hull_add in
    let hull = hull_or_bottom in
    let hull_of_plain (q : t) : P.t option =
      match q with
      | Clp ps -> hull_of_pieces ps
      | Exact s -> Some (hull_of_finset s)
      | _ -> None
    in
    (match t1, t2 with
     | Rel (o, a1), q2 when bitwidth q2 = 64 ->
       (match hull_of_plain q2 with
        | Some p2 -> canonical [ Rel (o, f (hull a1) p2) ]
        | None -> lift_binop op t1 t2)
     | q1, Rel (o, a2) when bitwidth q1 = 64 ->
       (match hull_of_plain q1 with
        | Some p1 -> canonical [ Rel (o, f p1 (hull a2)) ]
        | None -> lift_binop op t1 t2)
     | _ -> lift_binop op t1 t2)
  | Meet -> meet_rel t1 t2
  | Logand -> (
      match t1, t2 with
      | Rel (o, offs), plain -> logand_rel o offs plain
      | plain, Rel (o, offs) -> logand_rel o offs plain
      | _ -> top (Stdlib.max (bitwidth t1) (bitwidth t2)))
  | Logor | Logxor ->
    (* A width mismatch is the coercion pass's contract violation: top. *)
    if bitwidth t1 <> bitwidth t2 then top (Stdlib.max (bitwidth t1) (bitwidth t2))
    else (
      match t1, t2 with
      | Rel (o, offs), plain -> logor_rel_xor op o offs plain
      | plain, Rel (o, offs) -> logor_rel_xor op o offs plain
      | _ -> top (Stdlib.max (bitwidth t1) (bitwidth t2)))
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
         | Exact s -> Rel (Origin.Rip p, pieces_of_finset s)
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
type unop = Cbat_preimage.unop =
  | Lnot
  | Neg
  | Extract of int option * int
  | Cast of Bil.cast * int

(* THE unary table: the certified-nibble law, per origin — [Wrap] = the
   identity, [Image] = the certified image of the offsets into the
   plain tier, [Top] = the op keeps unknown base bits. *)
let unop_table (op : unop) ~(origin : Origin.t) : Hike_origin.un_row =
  let certified_bits = (Origin.facts origin).certified in
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
  | Many ps -> canonical (List.concat_map ps ~f:(fun q -> leaves (lift1 op q)))
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
      (Exact.extract ?hi ?lo:(Some lo)) t
  | Cast (c, sz) -> lift_unop (P.cast c sz) (Exact.cast c sz) t
  | Lnot -> blind_unop P.lnot Exact.lnot t
  | Neg -> blind_unop P.neg Exact.neg t

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
  (* A union across widths is a producer's collapse: top at the widest,
     so no mixed width reaches the single-width `Pieces` operations. *)
  | Union when bitwidth t1 <> bitwidth t2 -> top_w ()
  (* The union keeps one leaf per kind and per origin: a stack address
     joined with a plain value, a module address or another frame stays
     each of them. *)
  | Union -> join_plain t1 t2
  | Meet when (match t1 with Rel _ -> plain_is_top t2 | _ -> false) -> t1
  | Meet when (match t2 with Rel _ -> plain_is_top t1 | _ -> false) -> t2
  (* The shift count's width is incidental: a narrower plain count
     zero-extends to the shifted operand's width (the machine masks the
     count; the lift's count value is already masked). *)
  | Lshift | Rshift | Arshift
    when bitwidth t2 < bitwidth t1
         && (match t2 with Rel _ | Many _ -> false | _ -> true) ->
    lift2 op t1 (lift1 (Cast (Bil.UNSIGNED, bitwidth t1)) t2)
  (* The bitwise family zero-extends the narrower operand to the common
     width: no mismatch survives to the certified-bit computation. *)
  | Logand | Logor | Logxor
    when bitwidth t1 <> bitwidth t2
         && (match t1, t2 with Many _, _ | _, Many _ -> false | _ -> true) ->
    let w = Stdlib.max (bitwidth t1) (bitwidth t2) in
    let up t = if bitwidth t = w then t else lift1 (Cast (Bil.UNSIGNED, w)) t in
    lift2 op (up t1) (up t2)
  (* A mixed value is the union of its leaves: every other op
     distributes over them, so each relative leaf takes its own origin's
     row. *)
  | _ when (match t1, t2 with Many _, _ | _, Many _ -> true | _ -> false) ->
    canonical
      (List.concat_map (leaves t1) ~f:(fun q1 ->
           List.concat_map (leaves t2) ~f:(fun q2 -> leaves (lift2 op q1 q2))))
  | _ ->
  match t1, t2 with
  | Rel (Origin.Abs, offs), _ -> lift2 op (Clp offs) t2
  | _, Rel (Origin.Abs, offs) -> lift2 op t1 (Clp offs)
  | Rel (Origin.Rip p, a), Rel (Origin.Rip p', b)
    when Hike_section.equal p p' && (match op with Meet -> true | _ -> false) ->
    rip_wrap p (lift2 op (rip_plain a) (rip_plain b))
  | Rel (Origin.Rip p, a), (Clp _ | Exact _) when rip_keeps op ~left:true ->
    rip_wrap p (lift2 op (rip_plain a) t2)
  | (Clp _ | Exact _), Rel (Origin.Rip p, b) when rip_keeps op ~left:false ->
    rip_wrap p (lift2 op t1 (rip_plain b))
  | Rel (Origin.Rip _, a), _ -> lift2 op (rip_plain a) t2
  | _, Rel (Origin.Rip _, b) -> lift2 op t1 (rip_plain b)
  | _ -> if
    (match op with
     | Mul | Div | Sdiv | Modulo | Smodulo | Lshift | Rshift | Arshift
     | Concat ->
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
  (* A mixed value is the union of its leaves: each leaf loses the
     subtrahend, and a mixed subtrahend is removed leaf by leaf. *)
  | Many ps, _ -> canonical (List.concat_map ps ~f:(fun q -> leaves (diff q t2)))
  | _, Many qs -> List.fold qs ~init:t1 ~f:diff
  | Rel (Origin.Abs, offs), _ -> diff (Clp offs) t2
  | _, Rel (Origin.Abs, offs) -> diff t1 (Clp offs)
  | Rel (o1, a), Rel (o2, b)
    when Origin.equal o1 o2
         || (absolute_line o1 && absolute_line o2
             && Int64.equal (Origin.facts o1).base (Origin.facts o2).base) ->
    canonical [ Rel (o1, P.diff a b) ]
  | _, Rel (Origin.Rip _, b) -> diff t1 (rip_plain b)
  | _, Rel _ -> t1
  | Rel (Origin.Fs, _), _ -> t1
  | Rel (o, offs), plain ->
    (match plain_offsets o plain with
     | Some constraint_ -> canonical [ Rel (o, P.diff offs constraint_) ]
     | None -> t1)
  | _ ->
    let pair q1 q2 =
      if bitwidth q1 <> bitwidth q2 then [ q1 ]
      else
        match q1, q2 with
        | Exact s1, Exact s2 -> [ Exact (Exact.diff s1 s2) ]
        | Exact s, Clp ps ->
          [ Exact (Exact.filter s ~f:(fun w -> not (P.elem w ps))) ]
        | Clp ps, Exact s -> [ Clp (P.diff ps (pieces_of_finset s)) ]
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
  | Exact _ -> false
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
  | Exact _ -> false
  | Many _ -> false

(* A non-empty list whose every element passes; the empty mix is no shape. *)
let nonempty_for_all (xs : 'a list) ~(f : 'a -> bool) : bool =
  match xs with [] -> false | _ -> List.for_all xs ~f

let is_infinite t =
  match t with
  | Many ps -> nonempty_for_all ps ~f:piece_is_infinite
  | q -> piece_is_infinite q

let shape_pred (which : Clp.t -> bool) (t : t) : bool =
  let leaf q =
    match q with
    | Clp ps | Rel (_, ps) -> List.for_all (P.to_list ps) ~f:which
    | Exact _ -> false
    | Many _ -> false
  in
  match t with
  | Many ps -> nonempty_for_all ps ~f:leaf
  | q -> leaf q

let is_ascending t = shape_pred Clp.is_ascending t
let is_descending t = shape_pred Clp.is_descending t
let is_circular t = shape_pred Clp.is_circular t

let rec precedes t1 t2 : bool =
  match t1, t2 with
  | Rel (o1, a), Rel (o2, b) when Origin.equal o1 o2 -> P.precedes a b
  (* A mixed value is the union of its leaves: each leaf precedes the
     other side; a relative leaf precedes the same origin's leaf. *)
  | Many ps, _ -> List.for_all ps ~f:(fun q -> precedes q t2)
  | Rel (o, a), Many _ ->
    List.exists (rel_leaves t2) ~f:(fun (o', b) -> Origin.equal o o' && P.precedes a b)
  | _, Rel _ -> is_bottom t1
  | Rel _, _ -> precedes (to_plain t1) t2
  | Clp p1, Clp p2 -> P.precedes p1 p2
  | Exact s1, Exact s2 -> Exact.precedes s1 s2
  | Clp _, Exact _ -> false
  | Exact s, Clp _ -> P.precedes (hull_of_finset s) (as_hull t2)
  | _ -> P.precedes (as_hull t1) (as_hull t2)

(* Values with the same origin widen in its offsets.
   A plain pair widens BY KIND — two Clp leaves via [fp] (the positional
   piece widen), two Exact leaves via the tier's own widen — so a
   multi-piece value keeps its pieces through a growing widen (the
   interior exclusion survives).  A kind carried by one side only (the
   excess) hulls the plain pair — a widening must extrapolate, and the
   hull is the sound extrapolation.  The relative leaves widen apart
   from the plain ones, each origin in its own offsets: a relative leaf
   is never hulled into a plain value (a stack address would leave the
   stack key line).  A relative leaf only one side carries is kept. *)
let hull_join (f : Clp.t -> Clp.t -> Clp.t list) (fp : P.t -> P.t -> P.t) t1 t2 : t =
  (* The Exact tier widens by its own union while the union stays put;
     a union that grew has left the exact-small tier, so it escapes to
     the piece widen (the tier promotion the spec's Risks names) and the
     widening still extrapolates. *)
  let fs_widen (s1 : fset) (s2 : fset) : t =
    if Exact.precedes s2 s1 then Exact s1
    else if Exact.bitwidth s1 = Exact.bitwidth s2 then
      Clp (fp (pieces_of_finset s1) (pieces_of_finset s2))
    else
      let u = Exact.widen_join s1 s2 in
      if Exact.equal u s1 then Exact u
      else Clp (fp (pieces_of_finset s1) (pieces_of_finset s2))
  in
  let plain_hull p1 p2 =
    canonical [ Clp (P.widen_hulls f (as_hull p1) (as_hull p2)) ]
  in
  (* Two plain values: every kind carried by BOTH sides pairs with its
     own widen; a kind carried by one side only (the excess) hulls the
     whole pair — a one-sided piece has no partner to widen against, and
     a piece-preserving fold of it is the fixpoint's churn source. *)
  let plain_widen (p1 : t) (p2 : t) : t =
    let c1 = clp_leaf p1 and c2 = clp_leaf p2 in
    let s1 = fs_leaf p1 and s2 = fs_leaf p2 in
    let has o = Option.is_some o in
    if
      Stdlib.Int.equal (bitwidth p1) (bitwidth p2)
      && Bool.equal (has c1) (has c2)
      && Bool.equal (has s1) (has s2)
    then
      let parts =
        (match c1, c2 with Some a, Some b -> [ Clp (fp a b) ] | _ -> [])
        @ (match s1, s2 with Some a, Some b -> [ fs_widen a b ] | _ -> [])
      in
      if List.is_empty parts then plain_hull p1 p2 else canonical parts
    else plain_hull p1 p2
  in
  (* The plain leaves of a value, as one value. *)
  let plain_part (t : t) : t option =
    match List.filter (leaves t) ~f:(function Rel _ -> false | _ -> true) with
    | [] -> None
    | ps -> Some (canonical ps)
  in
  (* The relative leaves widen per origin, each against the pair's
     union: a leaf's next iterate need not contain the old one (a frame
     walked from its seed loses offset 0), and a widen of incomparable
     iterates only joins.  A leaf only one side carries is kept. *)
  let rec rel_widen r1 r2 : t list =
    match r1, r2 with
    | [], rest | rest, [] -> List.map rest ~f:(fun (o, a) -> Rel (o, a))
    | (o1, a) :: rest1, (o2, b) :: rest2 ->
      let c = Origin.compare o1 o2 in
      if c < 0 then Rel (o1, a) :: rel_widen rest1 r2
      else if c > 0 then Rel (o2, b) :: rel_widen r1 rest2
      else Rel (o1, fp a (P.union a b)) :: rel_widen rest1 rest2
  in
  match t1, t2 with
  | Rel (o1, a), Rel (o2, b) when Origin.equal o1 o2 ->
    canonical [ Rel (o1, fp a b) ]
  | _ ->
    let r1 = rel_leaves t1 and r2 = rel_leaves t2 in
    if List.is_empty r1 && List.is_empty r2 then plain_widen t1 t2
    else if not (Stdlib.Int.equal (bitwidth t1) (bitwidth t2)) then
      top (Stdlib.max (bitwidth t1) (bitwidth t2))
    else
      let plains =
        match plain_part t1, plain_part t2 with
        | None, None -> []
        | Some p, None | None, Some p -> leaves p
        | Some p1, Some p2 -> leaves (plain_widen p1 p2)
      in
      canonical (plains @ rel_widen r1 r2)

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
    P.bitwidth ps
  | Exact s -> Exact.get_idx s
  | Many ps ->
    List.fold ps ~init:0 ~f:(fun a q -> Stdlib.max a (get_idx q))

let pp_leaf ppf (t : t) =
  match t with
  | Rel (o, offs) ->
    Format.fprintf ppf "@[%s%a@]" (Origin.name o) (fun ppf ps ->
        match hull_of_pieces ps with
        | Some p -> P.pp ppf p
        | None -> ())
    offs
  | Clp ps ->
    (match hull_of_pieces ps with
     | Some p -> P.pp ppf p
     | None -> Format.fprintf ppf "_|_")
  | Exact s -> Exact.pp ppf s
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
let position_of_offset (o : int64) : int64 option =  checked_add stack_base o

(* The per-progression [min, max] positions of a stack-symbolic value's
   offsets — the disjoint runs the attribution clips per run instead of
   hulling (a two-band address keeps both bands in the portions). *)
let offset_runs (t : t) : (int64 * int64) list =
  match t with
  | Rel (o, offs) when Origin.names_stack_line o ->
    List.filter_map (P.to_list offs) ~f:(fun g ->
        let bounds =
          Option.bind (offsets_signed_extrema (P.of_progression g))
            ~f:(fun (lo, hi) -> Cbat_word.int64_pair lo hi)
        in
        Option.bind bounds ~f:(fun (lo, hi) ->
            match position_of_offset lo, position_of_offset hi with
            | Some lo, Some hi -> Some (lo, hi)
            | _ -> None))
  | _ -> []

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
        Base.Option.bind (Cbat_word.int64_pair lo hi) ~f:(fun (lo, hi) ->
            Base.Option.bind (position_of_offset lo) ~f:(fun lo ->
                Base.Option.map (position_of_offset hi) ~f:(fun hi -> (lo, hi))))
      | None ->
        (match min_elem t, max_elem t with
         | Some lo, Some hi -> Cbat_word.int64_pair lo hi
         | _ -> None)
    in
    match bounds with
    | Some (lo, hi) ->
      let is_inf = is_infinite t || Stdlib.Int64.compare lo hi > 0 in
      if is_inf then Infinite (lo, hi) else Range (lo, hi)
    | None -> unbounded_span

(* The elements, when the set is enumerable within [cap]; [None] = the
   base is symbolic or the count exceeds the budget. *)
#ifdef VSA_DEBUG
(* The value's constructor, for the churn diagnosis. *)
let tag (t : t) : string =
  match t with
  | Clp _ -> "Clp"
  | Exact _ -> "Exact"
  | Rel _ -> "Rel"
  | Many ps -> sprintf "Many%d" (List.length ps)
#endif

let enumerate ~(cap : int) (t : t) : word list option =
  if has_relative t then None else
#ifdef VSA_DEBUG
  if Cbat_word.gt_int (cardinality t) cap then begin
    Printf.eprintf "hike-dbg-enum: cap=%d card=%s tag=%s\n%!"
      cap (Cbat_word.to_string (cardinality t)) (tag t);
    None
  end else
#else
  if Cbat_word.gt_int (cardinality t) cap then None else
#endif
    Some (iter t)


(* Inverse dispatch mirrors the forward dispatch. Representation kernels
   operate on values; origins are interpreted only here. *)
let inverse_pieces = function
  | Clp p -> p
  | Exact s -> Exact.pieces s
  | q -> (
      match to_plain q with
      | Clp p -> p
      | Exact s -> Exact.pieces s
      | _ -> P.top (bitwidth q))

let inverse_meet a b =
  if is_bottom b then bottom (bitwidth a) else intersection a b

let inverse_plain1 op ~arg ~result =
  match (arg, result) with
  | Exact a, Exact r -> Exact (Exact.backward1 op ~arg:a ~result:r)
  | _ ->
      Clp
        (P.backward1 op ~arg:(inverse_pieces arg)
           ~result:(inverse_pieces result))

let inverse_plain2 op ~left ~right ~result =
  match (left, right, result) with
  | Exact a, Exact b, Exact r when Exact.count a * Exact.count b <= 4096 ->
      let x, y = Exact.backward2 op ~left:a ~right:b ~result:r in
      (Exact x, Exact y)
  | _ ->
      let x, y =
        P.backward2 op ~left:(inverse_pieces left) ~right:(inverse_pieces right)
          ~result:(inverse_pieces result)
      in
      (Clp x, Clp y)

let backward1 op ~arg ~result =
  if
    (not (is_bottom arg || is_bottom result))
    && not
         (Cbat_preimage.valid1 op ~arg:(bitwidth arg) ~result:(bitwidth result))
  then arg
  else
    let module I = Cbat_preimage in
    let one a r =
      if
        bitwidth a = bitwidth r
        &&
        match op with
        | I.Cast (_, n) -> n = bitwidth a
        | I.Extract (Some hi, 0) -> hi + 1 = bitwidth a
        | _ -> false
      then intersection a r
      else
        match a with
        | Rel (o, p) when absolute_line o ->
            inverse_meet a (inverse_plain1 op ~arg:(Clp p) ~result:(to_plain r))
        | Rel (o, p) ->
            let certified = (Origin.facts o).certified in
            let safe =
              match op with
              | I.Cast ((Bil.LOW | Bil.UNSIGNED), n) -> n <= certified
              | I.Extract (hi, _) ->
                  Option.value hi ~default:(bitwidth a - 1) < certified
              | _ -> false
            in
            if not safe then a
            else
              let base = Cbat_word.of_int64 ~width:64 (Origin.facts o).base in
              let shifted = P.translate p base in
              let narrowed =
                P.backward1 op ~arg:shifted ~result:(inverse_pieces r)
              in
              Rel
                (o, P.intersection p (P.translate narrowed (Cbat_word.neg base)))
        | _ -> inverse_plain1 op ~arg:a ~result:r
    in
    let answer =
      canonical
        (List.concat_map (leaves arg) ~f:(fun a ->
             List.map (leaves result) ~f:(fun r -> one a r)))
    in
    if is_bottom answer then bottom (bitwidth arg) else answer

let backward2 op ~left ~right ~result =
  if
    (not (is_bottom left || is_bottom right || is_bottom result))
    && not
         (Cbat_preimage.valid2 op ~left:(bitwidth left) ~right:(bitwidth right)
            ~result:(bitwidth result))
  then (left, right)
  else
    let module I = Cbat_preimage in
    let one a b r =
      match (a, b, r, op) with
      | Rel (o, x), Rel (p, y), _, I.Op Bil.MINUS when Origin.equal o p ->
          let u, v = inverse_plain2 op ~left:(Clp x) ~right:(Clp y) ~result:r in
          (Rel (o, inverse_pieces u), Rel (p, inverse_pieces v))
      | Rel (o, x), Rel (p, y), _, I.Op ((Bil.EQ | Bil.NEQ) as cmp)
        when Origin.equal o p ->
          let u, v =
            inverse_plain2 (I.Op cmp) ~left:(Clp x) ~right:(Clp y) ~result:r
          in
          (Rel (o, inverse_pieces u), Rel (p, inverse_pieces v))
      | Rel (o, x), (Clp _ | Exact _), Rel (p, z), I.Op (Bil.PLUS | Bil.MINUS)
        when Origin.equal o p ->
          let u, v = inverse_plain2 op ~left:(Clp x) ~right:b ~result:(Clp z) in
          (Rel (o, inverse_pieces u), v)
      | (Clp _ | Exact _), Rel (o, y), Rel (p, z), I.Op Bil.PLUS
        when Origin.equal o p ->
          let u, v = inverse_plain2 op ~left:a ~right:(Clp y) ~result:(Clp z) in
          (u, Rel (o, inverse_pieces v))
      | _, _, _, I.Op ((Bil.EQ | Bil.NEQ) as cmp) -> (
          let has0 = elem Cbat_word.b0 r and has1 = elem Cbat_word.b1 r in
          if has0 && has1 then (a, b)
          else if not (has0 || has1) then
            (bottom (bitwidth a), bottom (bitwidth b))
          else if Bool.equal has1 (Poly.equal cmp Bil.EQ) then
            let shared = intersection a b in
            (inverse_meet a shared, inverse_meet b shared)
          else
            ( (match singleton_of b with
              | Some k -> diff a (singleton k)
              | None -> a),
              match singleton_of a with
              | Some k -> diff b (singleton k)
              | None -> b ))
      | _ when has_relative a || has_relative b || has_relative r ->
          (* Unknown base bits cannot license a numerical inverse. *)
          (a, b)
      | _ ->
          let u, v =
            inverse_plain2 op ~left:(to_plain a) ~right:(to_plain b)
              ~result:(to_plain r)
          in
          (inverse_meet a u, inverse_meet b v)
    in
    let pairs =
      List.concat_map (leaves left) ~f:(fun a ->
          List.concat_map (leaves right) ~f:(fun b ->
              List.filter_map (leaves result) ~f:(fun r ->
                  let x, y = one a b r in
                  if is_bottom x || is_bottom y then None else Some (x, y))))
    in
    let assemble original f =
      let answer = canonical (List.map pairs ~f) in
      if is_bottom answer then bottom (bitwidth original) else answer
    in
    (assemble left fst, assemble right snd)
